"""Extract the trusted surface of each formalized result: its skeleton.

A theorem means what its *statement* means. To agree that a Lean declaration
says what the blueprint claims, a reader has to read the statement and every
definition the statement rests on, transitively -- and nothing else. Proofs are
the kernel's problem. The skeleton is exactly that reading list: a few lines a
person is expected to check, above a proof that may be orders of magnitude
longer and is checked by the kernel instead.

The closure is computed from elaborated terms, never from source text. A lexical
pass cannot see through ``open``, notation, implicit instances, or auto-bound
variables, and every miss silently shrinks the surface a reader is told to
trust. So the module writes a small Lean program, runs it with ``lake env
lean`` against the built project, and reads back one JSON line per declaration.
Only the *type* of a theorem is entered; the type and the *body* of a
definition are, because a definition's body is part of its meaning. Constants
outside the project are the trusted base and are listed by name rather than
expanded, so a reader sees that a statement uses Mathlib's notion rather than a
homemade one.

Generated companions -- constructors, projections, recursors, matchers,
equation lemmas -- are folded onto the declaration the reader sees in the
source, so a structure appears once, as the ``structure`` block, rather than as
five auto-generated names.

The output is deterministic and path-free like every other Autoform report: the
same sources produce the same JSON, and nothing here writes into the vault.
"""

from __future__ import annotations

import ctypes
import hashlib
import json
import os
import re
import secrets
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import warnings
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import psutil

from .graph import Graph, GraphValidationError, Node, load_graph
from .lean import SourceIndex, declaration_names, index_project, strip_lean_comments

try:  # Python 3.11+
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.10
    import tomli as tomllib  # type: ignore[no-redef]

SKELETON_SCHEMA = "autoform-skeleton/v2"
SEMANTIC_SCHEMA = "autoform-lean-expr/v2"

#: Every line the probe wants read back starts with this marker, so Lean's own
#: informational output can never be mistaken for a result.
PROBE_MARKER = "AUTOFORM_SKELETON "

#: Module roots whose declarations are never listed as assumptions: they are
#: the language itself, not mathematics a reader might want to double-check.
_CORE_MODULE_ROOTS = ("Init", "Lean", "Std", "Lake")

DEFAULT_PROBE_TIMEOUT = 600.0
DEFAULT_PROBE_OUTPUT_LIMIT = 64 * 1024 * 1024
_PROCESS_TERMINATION_GRACE = 2.0
_PROCESS_TOKEN_ENV = "_AUTOFORM_PROCESS_TOKEN"
_SNAPSHOT_FILE_LIMIT = 64 * 1024 * 1024
_PROJECT_CONTROL_FILES = (
    "lakefile.toml",
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
)

#: A callable that runs a probe and returns Lean's standard output. The default
#: shells out to ``lake env lean``; tests substitute a fake.
ProbeRunner = Callable[[str, Path], str]


class SkeletonError(RuntimeError):
    """A skeleton could not be extracted from the project."""

    def __init__(self, issues: list[str] | tuple[str, ...]) -> None:
        self.issues = tuple(issues)
        super().__init__("; ".join(self.issues))


@dataclass(frozen=True, slots=True)
class TrustedDeclaration:
    """One project declaration a reader must agree with."""

    name: str
    kind: str
    module: str
    path: str | None
    start_line: int | None
    end_line: int | None
    signature: str
    semantic: str
    depends: tuple[str, ...]
    source: str | None = None

    @property
    def lines(self) -> int:
        text = self.source if self.source is not None else self.signature
        return text.count("\n") + 1 if text else 0

    def as_dict(self) -> dict[str, object]:
        return {
            "depends": list(self.depends),
            "end_line": self.end_line,
            "kind": self.kind,
            "module": self.module,
            "name": self.name,
            "path": self.path,
            "signature": self.signature,
            "semantic": self.semantic,
            "source": self.source,
            "start_line": self.start_line,
        }


@dataclass(frozen=True, slots=True)
class DeclarationSkeleton:
    """The trusted surface of one root declaration."""

    name: str
    kind: str
    module: str
    path: str | None
    start_line: int | None
    end_line: int | None
    signature: str
    semantic: str
    lean_version: str
    depends: tuple[str, ...]
    trusted: tuple[TrustedDeclaration, ...]
    assumed: tuple[str, ...]
    assumed_semantics: tuple[tuple[str, str], ...]
    boundary_modules: tuple[tuple[str, str, str], ...]
    axioms: tuple[str, ...]
    axiom_semantics: tuple[tuple[str, str], ...]
    #: The declaration's own source when it is a definition, whose body is its
    #: meaning. A theorem's source holds its proof, which is never shown.
    source: str | None = None
    #: The statement as written in the source, cut before its value. The
    #: elaborated signature is authoritative; this is what the author typed,
    #: shown beside it so neither form can hide what the other shows.
    statement: str | None = None

    @property
    def defines(self) -> bool:
        """Whether the root is a definition rather than a proposition."""

        return self.kind not in {"theorem", "axiom"}

    @property
    def declaration_lines(self) -> int:
        """Source lines of the root declaration itself, proof included."""
        if self.start_line is None or self.end_line is None:
            return 0
        return self.end_line - self.start_line + 1

    @property
    def skeleton_lines(self) -> int:
        """Lines a reader has to read: the signature plus every trusted span."""
        own = self.source if self.source is not None else self.signature
        head = own.count("\n") + 1 if own else 0
        return head + sum(item.lines for item in self.trusted)

    @property
    def hash(self) -> str:
        """Fingerprint the probe's canonical elaborated meaning and trust boundary."""

        material = {
            "axioms": list(self.axioms),
            "axiom_semantics": [list(item) for item in self.axiom_semantics],
            "assumed": list(self.assumed),
            "assumed_semantics": [list(item) for item in self.assumed_semantics],
            "boundary_modules": [list(item) for item in self.boundary_modules],
            "depends": list(self.depends),
            "kind": self.kind,
            "lean_version": self.lean_version,
            "name": self.name,
            "semantic": self.semantic,
            "semantic_schema": SEMANTIC_SCHEMA,
            "trusted": [
                [item.name, item.kind, item.semantic, list(item.depends)]
                for item in self.trusted
            ],
        }
        return _sha256_id(json.dumps(material, sort_keys=True, ensure_ascii=False).encode())

    @property
    def evidence_hash(self) -> str:
        """Fingerprint the exact proof-free text presented to a reviewer."""

        return _sha256_id(self.blind_text().encode("utf-8"))

    def blind_text(self) -> str:
        """The skeleton with every comment removed, for an auditor who must not see intent.

        Testimony about what the code literally asserts is only evidence if
        its author did not know what the code was meant to say. Docstrings say
        exactly that, so they are stripped along with every other comment.
        Names stay: they are part of the code.
        """

        lines = [
            f"-- {self.kind} {self.name}",
            f"-- assumed from libraries: {', '.join(self.assumed) if self.assumed else 'none'}",
            f"-- axioms: {', '.join(self.axioms) if self.axioms else 'none'}",
            "",
            self.signature,
        ]
        own = strip_lean_comments(self.source or "").strip("\n")
        if own:
            lines.append(own)
        elif self.statement:
            written = strip_lean_comments(self.statement).strip("\n")
            if written:
                lines += ["-- as written:", written]
        for item in self.trusted:
            body = strip_lean_comments(item.source or "").strip("\n")
            # The elaborated signature restores what `variable` binders and
            # `open` leave implicit in the source, such as the type of `S`.
            lines += ["", f"-- {item.kind} {item.name}", f"-- signature: {item.signature}"]
            if body:
                lines.append(body)
        return "\n".join(lines) + "\n"

    def as_dict(self) -> dict[str, object]:
        return {
            "assumed": list(self.assumed),
            "assumed_semantics": [list(item) for item in self.assumed_semantics],
            "boundary_modules": [list(item) for item in self.boundary_modules],
            "axioms": list(self.axioms),
            "axiom_semantics": [list(item) for item in self.axiom_semantics],
            "declaration_lines": self.declaration_lines,
            "end_line": self.end_line,
            "evidence_hash": self.evidence_hash,
            "hash": self.hash,
            "kind": self.kind,
            "lean_version": self.lean_version,
            "module": self.module,
            "name": self.name,
            "path": self.path,
            "signature": self.signature,
            "semantic": self.semantic,
            "depends": list(self.depends),
            "skeleton_lines": self.skeleton_lines,
            "source": self.source,
            "start_line": self.start_line,
            "statement": self.statement,
            "trusted": [item.as_dict() for item in self.trusted],
        }


@dataclass(frozen=True, slots=True)
class NodeSkeleton:
    """The skeletons behind one blueprint article."""

    node_id: str
    article_path: str
    declarations: tuple[DeclarationSkeleton, ...]
    #: The source passage the article cites through a line locator, if any.
    #: This is the reference a faithfulness judge compares against.
    passage: str | None = None
    passage_locator: str | None = None

    def blind_text(self) -> str:
        """The article's declarations as one blind packet, for a faithfulness judge.

        A source theorem is often formalized by several declarations together,
        an existence half and a uniqueness half, say. Judged one at a time each
        is honestly incomplete; judged together they are the statement. An
        auditor asked what one declaration asserts still gets that declaration
        alone.
        """

        parts = [f"-- article with {len(self.declarations)} declaration(s)"]
        parts += [declaration.blind_text() for declaration in self.declarations]
        return "\n".join(parts)

    @property
    def hash(self) -> str:
        """One hash over all of an article's skeletons, printed as the article skeleton."""

        if len(self.declarations) == 1:
            return self.declarations[0].hash
        joined = "\n".join(sorted(item.hash for item in self.declarations))
        return _sha256_id(joined.encode())

    @property
    def evidence_hash(self) -> str:
        """Fingerprint the exact joint packet presented to a reviewer."""

        return _sha256_id(self.blind_text().encode("utf-8"))

    @property
    def review_hash(self) -> str:
        """Fingerprint the joint packet together with its cited source passage."""

        material = {
            "packet": self.evidence_hash,
            "passage": self.passage,
            "passage_locator": self.passage_locator,
        }
        return _sha256_id(json.dumps(material, sort_keys=True, ensure_ascii=False).encode())

    def as_dict(self) -> dict[str, object]:
        return {
            "article_path": self.article_path,
            "declarations": [item.as_dict() for item in self.declarations],
            "evidence_hash": self.evidence_hash,
            "hash": self.hash,
            "node_id": self.node_id,
            "passage": self.passage,
            "passage_locator": self.passage_locator,
            "review_hash": self.review_hash,
        }


@dataclass(frozen=True, slots=True)
class SkeletonReport:
    """Every skeleton the blueprint names, in article order."""

    nodes: tuple[NodeSkeleton, ...]
    unresolved: tuple[str, ...]
    schema: str = SKELETON_SCHEMA
    semantic_schema: str = SEMANTIC_SCHEMA

    @property
    def clean(self) -> bool:
        return not self.unresolved

    def node(self, node_id: str) -> NodeSkeleton | None:
        """Return the skeleton record of one article, if it has one."""

        return next((node for node in self.nodes if node.node_id == node_id), None)

    def declarations(self, node_id: str) -> tuple[DeclarationSkeleton, ...]:
        """Return the skeletons behind one article, or none."""

        node = self.node(node_id)
        return () if node is None else node.declarations

    def as_dict(self) -> dict[str, object]:
        return {
            "nodes": [node.as_dict() for node in self.nodes],
            "schema": self.schema,
            "semantic_schema": self.semantic_schema,
            "unresolved": list(self.unresolved),
        }

    def to_json(self) -> str:
        return json.dumps(self.as_dict(), sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def load_skeleton_report(path: str | Path) -> SkeletonReport:
    """Read a report written by :meth:`SkeletonReport.to_json` back into memory."""

    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise SkeletonError([f"cannot read skeleton report {path}: {exc}"]) from exc
    if (
        not isinstance(data, dict)
        or data.get("schema") != SKELETON_SCHEMA
        or data.get("semantic_schema") != SEMANTIC_SCHEMA
        or data.keys() != {"nodes", "schema", "semantic_schema", "unresolved"}
    ):
        raise SkeletonError([f"{path} is not an {SKELETON_SCHEMA} report"])
    raw_nodes = data["nodes"]
    unresolved = data["unresolved"]
    if not isinstance(raw_nodes, list) or not isinstance(unresolved, list) or not all(
        isinstance(issue, str) for issue in unresolved
    ):
        raise SkeletonError([f"{path} contains malformed skeleton report data"])
    nodes = tuple(_node_from_dict(node) for node in raw_nodes)
    if len({node.node_id for node in nodes}) != len(nodes):
        raise SkeletonError([f"{path} contains duplicate skeleton article ids"])
    report = SkeletonReport(nodes=nodes, unresolved=tuple(unresolved))
    return report


_NODE_REPORT_FIELDS = frozenset(
    {
        "article_path",
        "declarations",
        "evidence_hash",
        "hash",
        "node_id",
        "passage",
        "passage_locator",
        "review_hash",
    }
)
_DECLARATION_REPORT_FIELDS = frozenset(
    {
        "assumed",
        "boundary_modules",
        "assumed_semantics",
        "axiom_semantics",
        "axioms",
        "declaration_lines",
        "depends",
        "end_line",
        "evidence_hash",
        "hash",
        "kind",
        "lean_version",
        "module",
        "name",
        "path",
        "semantic",
        "signature",
        "skeleton_lines",
        "source",
        "start_line",
        "statement",
        "trusted",
    }
)
_TRUSTED_REPORT_FIELDS = frozenset(
    {
        "depends",
        "end_line",
        "kind",
        "module",
        "name",
        "path",
        "semantic",
        "signature",
        "source",
        "start_line",
    }
)


def _node_from_dict(item: object) -> NodeSkeleton:
    if not isinstance(item, dict) or item.keys() != _NODE_REPORT_FIELDS:
        raise SkeletonError(["malformed article in skeleton report"])
    node_id = _report_string(item.get("node_id"), "article id")
    article_path = _report_string(item.get("article_path"), f"article path for {node_id}")
    raw_declarations = item.get("declarations")
    if not isinstance(raw_declarations, list):
        raise SkeletonError([f"malformed declarations for {node_id} in skeleton report"])
    declarations = tuple(_declaration_from_dict(value) for value in raw_declarations)
    if len({declaration.name for declaration in declarations}) != len(declarations):
        raise SkeletonError([f"duplicate declarations for {node_id} in skeleton report"])
    passage = _report_optional_string(item.get("passage"), f"passage for {node_id}")
    locator = _report_optional_string(item.get("passage_locator"), f"passage locator for {node_id}")
    if (passage is None) != (locator is None):
        raise SkeletonError([f"mismatched passage fields for {node_id} in skeleton report"])
    node = NodeSkeleton(
        node_id=node_id,
        article_path=article_path,
        declarations=declarations,
        passage=passage,
        passage_locator=locator,
    )
    if item.get("hash") != node.hash:
        raise SkeletonError([f"invalid article hash for {node_id} in skeleton report"])
    if item.get("evidence_hash") != node.evidence_hash:
        raise SkeletonError([f"invalid article evidence hash for {node_id} in skeleton report"])
    if item.get("review_hash") != node.review_hash:
        raise SkeletonError([f"invalid article review hash for {node_id} in skeleton report"])
    return node


def _declaration_from_dict(item: object) -> DeclarationSkeleton:
    if not isinstance(item, dict) or item.keys() != _DECLARATION_REPORT_FIELDS:
        raise SkeletonError(["malformed declaration in skeleton report"])
    name = _report_string(item.get("name"), "declaration name")
    kind = _report_kind(item.get("kind"), name)
    semantic = _report_string(item.get("semantic"), f"semantic material for {name}")
    _validate_semantic_material(semantic, context=name, kind=kind)
    assumed = _report_string_tuple(item.get("assumed"), f"assumptions for {name}")
    assumed_semantics = _semantic_pairs(item.get("assumed_semantics"))
    boundary_modules = _report_module_identities(item.get("boundary_modules"), context=name)
    axioms = _report_string_tuple(item.get("axioms"), f"axioms for {name}")
    axiom_semantics = _semantic_pairs(item.get("axiom_semantics"))
    if tuple(key for key, _ in assumed_semantics) != assumed:
        raise SkeletonError([f"mismatched assumption semantics for {name}"])
    if tuple(key for key, _ in axiom_semantics) != axioms:
        raise SkeletonError([f"mismatched axiom semantics for {name}"])
    if assumed and not boundary_modules:
        raise SkeletonError([f"missing boundary module identities for {name}"])
    raw_trusted = item.get("trusted")
    if not isinstance(raw_trusted, list):
        raise SkeletonError([f"malformed trusted declarations for {name}"])
    trusted = tuple(_trusted_from_dict(value, root=name) for value in raw_trusted)
    if len({value.name for value in trusted}) != len(trusted):
        raise SkeletonError([f"duplicate trusted declarations for {name}"])
    source = _report_optional_string(item.get("source"), f"source for {name}")
    if kind in {"theorem", "axiom"} and source is not None:
        raise SkeletonError([f"proof-bearing source is forbidden for {kind} {name}"])
    if kind not in {"theorem", "axiom"} and (source is None or not source.strip()):
        raise SkeletonError([f"required source is missing for {kind} {name}"])
    declaration = DeclarationSkeleton(
        name=name,
        kind=kind,
        module=_report_string(item.get("module"), f"module for {name}"),
        path=_report_optional_string(item.get("path"), f"path for {name}"),
        start_line=_report_optional_int(item.get("start_line"), f"start line for {name}"),
        end_line=_report_optional_int(item.get("end_line"), f"end line for {name}"),
        signature=_report_string(item.get("signature"), f"signature for {name}"),
        semantic=semantic,
        lean_version=_report_string(item.get("lean_version"), f"Lean version for {name}"),
        depends=_report_string_tuple(item.get("depends"), f"dependencies for {name}"),
        trusted=trusted,
        assumed=assumed,
        assumed_semantics=assumed_semantics,
        boundary_modules=boundary_modules,
        axioms=axioms,
        axiom_semantics=axiom_semantics,
        source=source,
        statement=_report_optional_string(item.get("statement"), f"statement for {name}"),
    )
    _validate_report_ranges(declaration.start_line, declaration.end_line, context=name)
    if item.get("hash") != declaration.hash:
        raise SkeletonError([f"invalid declaration hash for {name} in skeleton report"])
    if item.get("evidence_hash") != declaration.evidence_hash:
        raise SkeletonError([f"invalid declaration evidence hash for {name} in skeleton report"])
    if item.get("declaration_lines") != declaration.declaration_lines:
        raise SkeletonError([f"invalid declaration line count for {name} in skeleton report"])
    if item.get("skeleton_lines") != declaration.skeleton_lines:
        raise SkeletonError([f"invalid skeleton line count for {name} in skeleton report"])
    return declaration


def _trusted_from_dict(item: object, *, root: str) -> TrustedDeclaration:
    if not isinstance(item, dict) or item.keys() != _TRUSTED_REPORT_FIELDS:
        raise SkeletonError([f"malformed trusted declaration for {root}"])
    name = _report_string(item.get("name"), f"trusted declaration name for {root}")
    kind = _report_kind(item.get("kind"), name)
    semantic = _report_string(item.get("semantic"), f"semantic material for {name}")
    _validate_semantic_material(semantic, context=name, kind=kind)
    source = _report_optional_string(item.get("source"), f"source for {name}")
    if kind in {"theorem", "axiom"} and source is not None:
        raise SkeletonError([f"proof-bearing source is forbidden for {kind} {name}"])
    if kind not in {"theorem", "axiom"} and (source is None or not source.strip()):
        raise SkeletonError([f"required source is missing for {kind} {name}"])
    trusted = TrustedDeclaration(
        name=name,
        kind=kind,
        module=_report_string(item.get("module"), f"module for {name}"),
        path=_report_optional_string(item.get("path"), f"path for {name}"),
        start_line=_report_optional_int(item.get("start_line"), f"start line for {name}"),
        end_line=_report_optional_int(item.get("end_line"), f"end line for {name}"),
        signature=_report_string(item.get("signature"), f"signature for {name}"),
        semantic=semantic,
        depends=_report_string_tuple(item.get("depends"), f"dependencies for {name}"),
        source=source,
    )
    _validate_report_ranges(trusted.start_line, trusted.end_line, context=name)
    return trusted


def _report_string(value: object, context: str) -> str:
    if not isinstance(value, str) or not value:
        raise SkeletonError([f"invalid {context} in skeleton report"])
    return value


def _report_optional_string(value: object, context: str) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str):
        raise SkeletonError([f"invalid {context} in skeleton report"])
    return value


def _report_optional_int(value: object, context: str) -> int | None:
    if value is None:
        return None
    if type(value) is not int:
        raise SkeletonError([f"invalid {context} in skeleton report"])
    return value


def _report_string_tuple(value: object, context: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        raise SkeletonError([f"invalid {context} in skeleton report"])
    if len(value) != len(set(value)):
        raise SkeletonError([f"duplicate {context} in skeleton report"])
    return tuple(value)


def _report_kind(value: object, context: str) -> str:
    if not isinstance(value, str) or value not in _DECLARATION_KINDS:
        raise SkeletonError([f"invalid declaration kind for {context} in skeleton report"])
    return value


def _report_module_identities(value: object, *, context: str) -> tuple[tuple[str, str, str], ...]:
    entries = _module_file_entries(value, context=context)
    for module, file_kind, digest in entries:
        if not re.fullmatch(r"sha256:[0-9a-f]{64}", digest):
            raise SkeletonError([f"invalid {file_kind} identity for module {module} in skeleton report"])
    return entries


def _validate_report_ranges(start: int | None, end: int | None, *, context: str) -> None:
    if (start is None) != (end is None) or (
        start is not None and end is not None and (start < 1 or end < start)
    ):
        raise SkeletonError([f"invalid source range for {context} in skeleton report"])


def _sha256_id(content: bytes) -> str:
    return f"sha256:{hashlib.sha256(content).hexdigest()}"


def _read_snapshot_pass(
    path: Path, *, keep_content: bool
) -> tuple[bytes, tuple[int, str]] | None:
    """Read one bounded regular-file pass."""

    try:
        path_metadata = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise SkeletonError([f"cannot inspect skeleton input {path}: {exc}"]) from exc
    if not stat.S_ISREG(path_metadata.st_mode):
        raise SkeletonError([f"skeleton input is not a regular file: {path}"])
    flags = (
        os.O_RDONLY
        | getattr(os, "O_BINARY", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise SkeletonError([f"cannot open skeleton input {path}: {exc}"]) from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise SkeletonError([f"skeleton input is not a regular file: {path}"])
        digest = hashlib.sha256()
        chunks: list[bytes] = []
        size = 0
        while True:
            block = os.read(descriptor, 64 * 1024)
            if not block:
                break
            size += len(block)
            if size > _SNAPSHOT_FILE_LIMIT:
                raise SkeletonError(
                    [f"skeleton input exceeds the {_SNAPSHOT_FILE_LIMIT}-byte limit: {path}"]
                )
            digest.update(block)
            if keep_content:
                chunks.append(block)
    except OSError as exc:
        raise SkeletonError([f"cannot read skeleton input {path}: {exc}"]) from exc
    finally:
        os.close(descriptor)
    return b"".join(chunks), (size, digest.hexdigest())


def _read_snapshot_file(path: Path) -> tuple[bytes, tuple[int, str]] | None:
    """Read a bounded regular file twice to reject concurrent content changes."""

    captured = _read_snapshot_pass(path, keep_content=True)
    verified = _read_snapshot_pass(path, keep_content=False)
    captured_fingerprint = None if captured is None else captured[1]
    verified_fingerprint = None if verified is None else verified[1]
    if captured_fingerprint != verified_fingerprint:
        raise SkeletonError([f"skeleton input changed while it was read: {path}"])
    return captured


def _snapshot_regular_file(path: Path) -> tuple[int, str] | None:
    captured = _read_snapshot_file(path)
    return None if captured is None else captured[1]


def _project_control_snapshot(root: Path) -> tuple[tuple[str, tuple[int, str] | None], ...]:
    """Fingerprint the Lake inputs that select the compiled environment."""

    return tuple(
        (name, _snapshot_regular_file(root / name)) for name in _PROJECT_CONTROL_FILES
    )


def _graph_snapshot(graph: Graph) -> tuple[tuple[str, str, str], ...]:
    """Fingerprint the exact Markdown articles used to choose declarations."""

    return tuple(
        (
            node.id,
            _article_path(node, graph),
            node.source_sha256 or "",
        )
        for node in sorted(graph.nodes.values(), key=lambda item: item.id)
    )


def _remember_descendants(
    process: subprocess.Popen[bytes],
    descendants: dict[tuple[int, float], psutil.Process],
) -> None:
    """Retain handles for children that may outlive their immediate parent."""

    try:
        children = psutil.Process(process.pid).children(recursive=True)
    except (psutil.Error, OSError):
        return
    for child in children:
        try:
            descendants[(child.pid, child.create_time())] = child
        except (psutil.Error, OSError):
            continue


def _remember_tagged_processes(
    token: str,
    descendants: dict[tuple[int, float], psutil.Process],
) -> None:
    """Find descendants that escaped the original parent and process group."""

    for candidate in psutil.process_iter():
        if candidate.pid == os.getpid():
            continue
        try:
            if candidate.environ().get(_PROCESS_TOKEN_ENV) == token:
                descendants[(candidate.pid, candidate.create_time())] = candidate
        except (psutil.Error, OSError):
            continue


def _process_is_alive(process: psutil.Process) -> bool:
    try:
        return process.is_running() and process.status() != psutil.STATUS_ZOMBIE
    except (psutil.Error, OSError):
        return False


def _process_group_is_alive(pid: int) -> bool:
    if os.name != "posix":
        return False
    try:
        os.killpg(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True


def _remaining(deadline: float) -> float:
    return max(0.0, deadline - time.perf_counter())


def _join_readers(readers: list[threading.Thread], *, deadline: float) -> bool:
    for reader in readers:
        reader.join(timeout=_remaining(deadline))
    return not any(reader.is_alive() for reader in readers)


def _terminate_process_tree(
    process: subprocess.Popen[bytes],
    descendants: dict[tuple[int, float], psutil.Process],
    *,
    deadline: float,
    token: str,
) -> None:
    """Best-effort termination of a command and every descendant observed."""

    _remember_descendants(process, descendants)
    _remember_tagged_processes(token, descendants)
    children = [child for child in descendants.values() if _process_is_alive(child)]
    phase_start = time.perf_counter()
    available = _remaining(deadline)
    process_deadline = phase_start + available * 0.8
    term_deadline = phase_start + available * 0.4
    if os.name == "posix":
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError, OSError):
            pass
    else:  # pragma: no cover - Windows-specific best effort
        for child in reversed(children):
            try:
                child.terminate()
            except psutil.Error:
                pass
        if process.poll() is None:
            try:
                process.terminate()
            except OSError:
                pass

    if process.poll() is None:
        try:
            process.wait(timeout=_remaining(term_deadline))
        except (OSError, subprocess.TimeoutExpired):
            pass
    if children and _remaining(term_deadline) > 0:
        try:
            psutil.wait_procs(children, timeout=_remaining(term_deadline))
        except (psutil.Error, OSError):
            pass

    if os.name == "posix" and _process_group_is_alive(process.pid):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
    _remember_tagged_processes(token, descendants)
    for child in descendants.values():
        if _process_is_alive(child):
            try:
                child.kill()
            except psutil.Error:
                pass
    if process.poll() is None:
        try:
            process.kill()
        except OSError:
            pass
    try:
        process.wait(timeout=_remaining(process_deadline))
    except (OSError, subprocess.TimeoutExpired):
        pass
    live_children = [
        child for child in descendants.values() if _process_is_alive(child)
    ]
    if live_children and _remaining(process_deadline) > 0:
        try:
            psutil.wait_procs(live_children, timeout=_remaining(process_deadline))
        except (psutil.Error, OSError):
            pass


def _run_bounded_command(
    command: list[str],
    *,
    cwd: Path,
    timeout: float,
    context: str,
    env: dict[str, str] | None = None,
    output_limit: int = DEFAULT_PROBE_OUTPUT_LIMIT,
) -> subprocess.CompletedProcess[str]:
    """Run one command with bounded output, time, and descendant lifetime."""

    if timeout <= 0:
        raise SkeletonError([f"{context} timed out"])
    if output_limit < 1:
        raise ValueError("output_limit must be positive")
    popen_options: dict[str, object] = {}
    if os.name == "posix":
        popen_options["start_new_session"] = True
    elif os.name == "nt":  # pragma: no cover - Windows-specific best effort
        popen_options["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    process: subprocess.Popen[bytes] | None = None
    readers: list[threading.Thread] = []
    chunks: dict[str, list[bytes]] = {"stdout": [], "stderr": []}
    capture_lock = threading.Lock()
    overflow = threading.Event()
    reader_failure = threading.Event()
    reader_errors: list[BaseException] = []
    captured = 0

    def drain(name: str, stream: object) -> None:
        nonlocal captured
        try:
            while True:
                block = stream.read(64 * 1024)  # type: ignore[attr-defined]
                if not block:
                    return
                with capture_lock:
                    remaining = max(0, output_limit - captured)
                    if remaining:
                        chunks[name].append(block[:remaining])
                    if len(block) > remaining:
                        overflow.set()
                    captured = min(output_limit + 1, captured + len(block))
        except (OSError, ValueError) as exc:
            reader_errors.append(exc)
            reader_failure.set()
        finally:
            try:
                stream.close()  # type: ignore[attr-defined]
            except OSError:
                pass

    descendants: dict[tuple[int, float], psutil.Process] = {}
    token = secrets.token_hex(16)
    process_env = os.environ.copy() if env is None else env.copy()
    process_env[_PROCESS_TOKEN_ENV] = token
    deadline = time.monotonic() + timeout
    cleanup_deadline: float | None = None
    failure: SkeletonError | None = None
    terminated = False
    try:
        try:
            process = subprocess.Popen(
                command,
                cwd=str(cwd),
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=process_env,
                close_fds=True,
                **popen_options,
            )
        except OSError as exc:
            raise SkeletonError([f"{context} failed: {exc}"]) from exc
        assert process.stdout is not None and process.stderr is not None
        for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
            reader = threading.Thread(target=drain, args=(name, stream), daemon=True)
            reader.start()
            readers.append(reader)
        while process.poll() is None:
            _remember_descendants(process, descendants)
            if reader_failure.is_set():
                failure = SkeletonError(
                    [f"{context} output could not be read: {reader_errors[0]}"]
                )
                break
            if overflow.is_set():
                failure = SkeletonError(
                    [f"{context} exceeded the {output_limit}-byte output limit"]
                )
                break
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                failure = SkeletonError([f"{context} timed out after {timeout:g} seconds"])
                break
            overflow.wait(min(0.05, remaining))
        _remember_descendants(process, descendants)
        _remember_tagged_processes(token, descendants)
        live_descendants = any(
            _process_is_alive(descendant) for descendant in descendants.values()
        )
        live_group = _process_group_is_alive(process.pid)
        if failure is None and (live_descendants or live_group):
            failure = SkeletonError([f"{context} left descendant processes running"])
        cleanup_deadline = time.perf_counter() + _PROCESS_TERMINATION_GRACE
        if failure is not None:
            _terminate_process_tree(
                process,
                descendants,
                deadline=cleanup_deadline,
                token=token,
            )
            terminated = True
        reader_deadline = cleanup_deadline
        if failure is None:
            reader_start = time.perf_counter()
            reader_deadline = reader_start + _remaining(cleanup_deadline) * 0.2
        if not _join_readers(readers, deadline=reader_deadline):
            if failure is None:
                failure = SkeletonError(
                    [f"{context} left descendant processes holding its output pipes open"]
                )
            if not terminated:
                _terminate_process_tree(
                    process,
                    descendants,
                    deadline=cleanup_deadline,
                    token=token,
                )
                terminated = True
            _join_readers(readers, deadline=cleanup_deadline)
        if failure is not None:
            raise failure
        if overflow.is_set():
            raise SkeletonError([f"{context} exceeded the {output_limit}-byte output limit"])
        if reader_errors:
            raise SkeletonError([f"{context} output could not be read: {reader_errors[0]}"])
        try:
            stdout = b"".join(chunks["stdout"]).decode("utf-8")
            stderr = b"".join(chunks["stderr"]).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SkeletonError([f"{context} emitted invalid UTF-8 output"]) from exc
        return subprocess.CompletedProcess(command, process.returncode, stdout=stdout, stderr=stderr)
    except BaseException:
        if cleanup_deadline is None:
            cleanup_deadline = time.perf_counter() + _PROCESS_TERMINATION_GRACE
        if process is not None and not terminated:
            _terminate_process_tree(
                process,
                descendants,
                deadline=cleanup_deadline,
                token=token,
            )
        _join_readers(readers, deadline=cleanup_deadline)
        raise
    finally:
        if process is not None:
            for index, stream in enumerate((process.stdout, process.stderr)):
                if stream is None:
                    continue
                if index < len(readers) and readers[index].is_alive():
                    continue
                else:
                    stream.close()


# --------------------------------------------------------------------------- #
# Lean project layout
# --------------------------------------------------------------------------- #


@dataclass(frozen=True, slots=True)
class LeanLibrary:
    """One ``lean_lib`` target: where its modules live and what they are called."""

    name: str
    src_dir: Path
    roots: tuple[str, ...]


def lean_libraries(lean_root: str | Path) -> tuple[LeanLibrary, ...]:
    """Read the project's library targets from its Lake configuration.

    A TOML manifest is read directly. A Lean manifest is evaluated by Lake
    itself through ``lake translate-config``, the same way the generated verify
    workflow reads the root package name, so both manifest languages are
    handled without a second parser for Lean syntax.
    """

    root = Path(lean_root).expanduser().resolve()
    toml = root / "lakefile.toml"
    toml_snapshot = _read_snapshot_file(toml)
    lakefile = root / "lakefile.lean"
    lakefile_snapshot = _read_snapshot_file(lakefile)
    if toml_snapshot is not None:
        text = toml_snapshot[0]
    elif lakefile_snapshot is not None:
        text = _translate_lakefile(root)
    else:
        raise SkeletonError([f"no lakefile.toml or lakefile.lean in {root}"])
    try:
        config = tomllib.loads(text.decode("utf-8"))
    except (UnicodeError, tomllib.TOMLDecodeError) as exc:
        raise SkeletonError([f"cannot parse the Lake configuration of {root}: {exc}"]) from exc

    libraries: list[LeanLibrary] = []
    for entry in config.get("lean_lib", []) or []:
        if not isinstance(entry, dict) or not isinstance(entry.get("name"), str):
            continue
        name = entry["name"]
        src_dir = root / str(entry.get("srcDir", "."))
        roots = entry.get("roots")
        if not isinstance(roots, list) or not all(isinstance(item, str) for item in roots):
            roots = [name]
        libraries.append(LeanLibrary(name=name, src_dir=src_dir.resolve(), roots=tuple(roots)))
    if not libraries:
        package = config.get("name")
        if isinstance(package, str) and package:
            libraries.append(LeanLibrary(name=package, src_dir=root, roots=(package,)))
    if not libraries:
        raise SkeletonError([f"the Lake configuration of {root} declares no library"])
    return tuple(libraries)


def _translate_lakefile(root: Path) -> bytes:
    lake = shutil.which("lake")
    if lake is None:
        raise SkeletonError(["lake is not on PATH, so lakefile.lean cannot be evaluated"])
    with tempfile.TemporaryDirectory(prefix="autoform-skeleton-") as scratch:
        target = Path(scratch) / "lakefile.toml"
        result = _run_bounded_command(
            [lake, "translate-config", "toml", str(target)],
            cwd=root,
            timeout=120,
            context="lake translate-config",
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()[:300]
            raise SkeletonError([f"lake translate-config failed: {detail}"])
        translated = _read_snapshot_file(target)
        if translated is None:
            raise SkeletonError(["lake translate-config failed: translated configuration is missing"])
        return translated[0]


def module_of(path: Path, libraries: tuple[LeanLibrary, ...]) -> str | None:
    """Return the Lean module name of a source file, or ``None`` if no library holds it."""

    resolved = path.resolve()
    best: tuple[int, str] | None = None
    for library in libraries:
        try:
            relative = resolved.relative_to(library.src_dir)
        except ValueError:
            continue
        if relative.suffix != ".lean":
            continue
        module = ".".join(relative.with_suffix("").parts)
        depth = len(library.src_dir.parts)
        if best is None or depth > best[0]:
            best = (depth, module)
    return None if best is None else best[1]


def path_of(module: str, libraries: tuple[LeanLibrary, ...], lean_root: Path) -> str | None:
    """Return the repository-relative source path of ``module``, if it exists."""

    parts = module.split(".")
    for library in libraries:
        candidate = library.src_dir.joinpath(*parts).with_suffix(".lean")
        if candidate.is_file():
            return _relative(candidate, lean_root)
    return None


def _relative(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.name


# --------------------------------------------------------------------------- #
# The probe
# --------------------------------------------------------------------------- #

def _probe_template() -> str:
    """The Lean probe, kept beside the other generated-file sources under templates/."""

    return (Path(__file__).parent / "probes" / "skeleton_probe.lean").read_text(encoding="utf-8")


def render_probe(
    *,
    imports: tuple[str, ...],
    roots: tuple[str, ...],
    project_roots: tuple[str, ...],
) -> str:
    """Render the Lean program that extracts the skeleton of every root."""

    if not roots:
        raise SkeletonError(["refusing to render a probe with no declarations"])
    if not imports:
        raise SkeletonError(["refusing to render a probe with no imports"])
    return _probe_template().format(
        core_roots=", ".join(_lean_name(name) for name in _CORE_MODULE_ROOTS),
        imports="\n".join(f"import {module}" for module in sorted(set(imports))),
        marker=PROBE_MARKER,
        project_roots=", ".join(_lean_name(name) for name in sorted(set(project_roots))),
        roots=", ".join(f"({json.dumps(name, ensure_ascii=False)}, {_lean_name(name)})" for name in roots),
    )


def _lean_name(name: str) -> str:
    """Spell a Lean name as a term without trusting Lean to parse it."""

    result = "Name.anonymous"
    for part, quoted in _lean_name_parts(name):
        if not quoted and part.isascii() and part.isdigit():
            result = f"Name.num ({result}) {int(part)}"
        else:
            result = f"Name.str ({result}) {json.dumps(part, ensure_ascii=False)}"
    return result


def _lean_name_parts(name: str) -> tuple[tuple[str, bool], ...]:
    """Parse the dot-separated surface spelling of a Lean ``Name``.

    Guillemets quote one name component, so ``A.«b.c d»`` has two components,
    not three. Constructing the name structurally keeps all such spellings out
    of generated Lean syntax.
    """

    parts: list[tuple[str, bool]] = []
    index = 0
    while index < len(name):
        if name[index] == "«":
            close = name.find("»", index + 1)
            if close < 0 or close == index + 1:
                raise SkeletonError([f"invalid Lean declaration name: {name!r}"])
            parts.append((name[index + 1 : close], True))
            index = close + 1
        else:
            end = name.find(".", index)
            end = len(name) if end < 0 else end
            part = name[index:end]
            if not part or any(character.isspace() for character in part) or "«" in part or "»" in part:
                raise SkeletonError([f"invalid Lean declaration name: {name!r}"])
            parts.append((part, False))
            index = end
        if index == len(name):
            break
        if name[index] != ".":
            raise SkeletonError([f"invalid Lean declaration name: {name!r}"])
        index += 1
        if index == len(name):
            raise SkeletonError([f"invalid Lean declaration name: {name!r}"])
    if not parts:
        raise SkeletonError(["invalid empty Lean declaration name"])
    return tuple(parts)


def _probe_modules(probe: str) -> tuple[str, ...]:
    """Read the generated probe's leading project imports."""

    modules: list[str] = []
    for line in probe.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if not stripped.startswith("import "):
            break
        module = stripped.removeprefix("import ").strip()
        if not module or any(character.isspace() for character in module):
            raise SkeletonError(["the generated skeleton probe contains an invalid import"])
        modules.append(module)
    if not modules:
        raise SkeletonError(["the generated skeleton probe contains no project imports"])
    return tuple(dict.fromkeys(modules))


def _check_artifacts_fresh(
    lake: str, lean_root: Path, modules: tuple[str, ...], *, timeout: float
) -> None:
    """Ask Lake to prove that imported artifacts match their exact inputs."""

    result = _run_bounded_command(
        [lake, "--rehash", "--no-build", "build", *modules],
        cwd=lean_root,
        timeout=timeout,
        context="cannot verify Lean build freshness",
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise SkeletonError([f"Lean build artifacts are stale; run `lake build` before extracting skeletons\n{detail}"])


def run_probe(probe: str, lean_root: Path, *, timeout: float = DEFAULT_PROBE_TIMEOUT) -> str:
    """Run ``probe`` with ``lake env lean`` inside the built project."""

    lake = shutil.which("lake")
    if lake is None:
        raise SkeletonError(["lake is not on PATH; a built Lean project is required to extract skeletons"])
    if not (lean_root / "lake-manifest.json").is_file():
        raise SkeletonError(
            ["lake-manifest.json is missing; run `lake build` before extracting skeletons"]
        )
    modules = _probe_modules(probe)
    deadline = time.monotonic() + timeout
    _check_artifacts_fresh(
        lake,
        lean_root,
        modules,
        timeout=max(0.0, deadline - time.monotonic()),
    )
    env = os.environ.copy()
    env.pop("PYTHONPATH", None)
    with tempfile.TemporaryDirectory(prefix="autoform-skeleton-") as scratch:
        source = Path(scratch) / "AutoformSkeletonProbe.lean"
        source.write_text(probe, encoding="utf-8")
        result = _run_bounded_command(
            [lake, "env", "lean", str(source)],
            cwd=lean_root,
            timeout=max(0.0, deadline - time.monotonic()),
            context="lake env lean",
            env=env,
        )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise SkeletonError([f"the skeleton probe failed; is the project built with `lake build`?\n{detail}"])
    return result.stdout


_FOUND_RECORD_FIELDS = frozenset(
    {
        "assumed",
        "boundary_modules",
        "assumed_semantics",
        "axiom_semantics",
        "axioms",
        "depends",
        "found",
        "kind",
        "lean_version",
        "module",
        "range",
        "root",
        "semantic",
        "semantic_schema",
        "signature",
        "source",
        "statement_source",
        "trusted",
    }
)
_TRUSTED_RECORD_FIELDS = frozenset(
    {"depends", "kind", "module", "name", "range", "semantic", "semantic_schema", "signature", "source"}
)
_DECLARATION_KINDS = frozenset(
    {"axiom", "class", "constructor", "def", "inductive", "instance", "opaque", "quot", "recursor", "structure", "theorem"}
)


def parse_probe_output(
    text: str, *, expected_roots: tuple[str, ...] | None = None
) -> dict[str, dict[str, object]]:
    """Return strictly validated probe records, keyed by requested root name."""

    records: dict[str, dict[str, object]] = {}
    expected = None if expected_roots is None else set(expected_roots)
    for line in text.splitlines():
        if not line.startswith(PROBE_MARKER):
            continue
        try:
            record = json.loads(line[len(PROBE_MARKER) :])
        except json.JSONDecodeError as exc:
            raise SkeletonError([f"the skeleton probe emitted invalid JSON: {exc}"]) from exc
        if not isinstance(record, dict) or not isinstance(record.get("root"), str) or not record["root"]:
            raise SkeletonError(["the skeleton probe emitted a record without a root name"])
        root = record["root"]
        if root in records:
            raise SkeletonError([f"the skeleton probe emitted duplicate records for {root}"])
        if expected is not None and root not in expected:
            raise SkeletonError([f"the skeleton probe emitted an unrequested root: {root}"])
        _validate_probe_record(record, root=root)
        records[root] = record
    return records


def _validate_probe_record(record: dict[str, object], *, root: str) -> None:
    found = record.get("found")
    if type(found) is not bool:
        raise SkeletonError([f"the skeleton probe emitted a non-boolean found field for {root}"])
    expected_fields = _FOUND_RECORD_FIELDS if found else frozenset({"found", "root"})
    if record.keys() != expected_fields:
        raise SkeletonError([f"the skeleton probe emitted invalid fields for {root}"])
    if not found:
        return
    _require_kind(record.get("kind"), context=root)
    _require_nonempty_string(record.get("lean_version"), field="lean_version", context=root)
    _require_semantic(record, context=root, kind=str(record["kind"]))
    _require_nonempty_string(record.get("module"), field="module", context=root)
    _require_nonempty_string(record.get("signature"), field="signature", context=root)
    _require_range(record.get("range"), context=root)
    _require_probe_source(record.get("source"), kind=str(record["kind"]), context=root)
    if record.get("statement_source") is not None and not isinstance(record["statement_source"], str):
        raise SkeletonError([f"the skeleton probe emitted an invalid statement_source for {root}"])
    for field in ("depends", "assumed", "axioms"):
        _require_string_list(record.get(field), field=field, context=root)
    _require_semantic_pairs(
        record.get("assumed_semantics"),
        names=record["assumed"],
        field="assumed_semantics",
        context=root,
    )
    boundary_modules = _require_module_files(record.get("boundary_modules"), context=root)
    if record["assumed"] and not boundary_modules:
        raise SkeletonError([f"the skeleton probe omitted boundary module files for {root}"])
    _require_semantic_pairs(
        record.get("axiom_semantics"),
        names=record["axioms"],
        field="axiom_semantics",
        context=root,
    )
    trusted = record.get("trusted")
    if not isinstance(trusted, list) or not all(isinstance(item, dict) for item in trusted):
        raise SkeletonError([f"the skeleton probe emitted an invalid trusted field for {root}"])
    seen: set[str] = set()
    for item in trusted:
        _validate_trusted_record(item, root=root)
        name = item["name"]
        if name in seen:
            raise SkeletonError([f"the skeleton probe emitted duplicate trusted declaration {name} for {root}"])
        seen.add(name)


def _validate_trusted_record(record: dict[str, object], *, root: str) -> None:
    name = record.get("name")
    context = f"{root} trusted declaration {name}" if isinstance(name, str) and name else root
    if record.keys() != _TRUSTED_RECORD_FIELDS:
        raise SkeletonError([f"the skeleton probe emitted invalid trusted fields for {context}"])
    _require_nonempty_string(name, field="name", context=root)
    _require_kind(record.get("kind"), context=context)
    _require_semantic(record, context=context, kind=str(record["kind"]))
    _require_nonempty_string(record.get("module"), field="module", context=context)
    _require_nonempty_string(record.get("signature"), field="signature", context=context)
    _require_range(record.get("range"), context=context)
    _require_probe_source(record.get("source"), kind=str(record["kind"]), context=context)
    _require_string_list(record.get("depends"), field="depends", context=context)


def _require_semantic(record: dict[str, object], *, context: str, kind: str) -> None:
    if record.get("semantic_schema") != SEMANTIC_SCHEMA:
        raise SkeletonError([f"the skeleton probe emitted an unsupported semantic schema for {context}"])
    semantic = record.get("semantic")
    _require_nonempty_string(semantic, field="semantic", context=context)
    assert isinstance(semantic, str)
    _validate_semantic_material(semantic, context=context, kind=kind)


def _require_kind(value: object, *, context: str) -> None:
    if not isinstance(value, str) or value not in _DECLARATION_KINDS:
        raise SkeletonError([f"the skeleton probe emitted an invalid declaration kind for {context}"])


def _require_nonempty_string(value: object, *, field: str, context: str) -> None:
    if not isinstance(value, str) or not value:
        raise SkeletonError([f"the skeleton probe emitted an invalid {field} field for {context}"])


def _require_probe_source(value: object, *, kind: str, context: str) -> None:
    if value is not None and not isinstance(value, str):
        raise SkeletonError([f"the skeleton probe emitted an invalid source field for {context}"])
    if kind in {"theorem", "axiom"} and value is not None:
        raise SkeletonError([f"the skeleton probe emitted proof-bearing source for {context}"])
    if kind not in {"theorem", "axiom"} and (not isinstance(value, str) or not value.strip()):
        raise SkeletonError([f"the skeleton probe omitted required source for {context}"])


def _require_range(value: object, *, context: str) -> None:
    if value is None:
        return
    if not isinstance(value, list) or len(value) != 2:
        raise SkeletonError([f"the skeleton probe emitted an invalid range for {context}"])
    start, end = value
    if type(start) is not int or type(end) is not int or start < 1 or end < start:
        raise SkeletonError([f"the skeleton probe emitted an invalid range for {context}"])


def _require_string_list(value: object, *, field: str, context: str) -> None:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        raise SkeletonError([f"the skeleton probe emitted an invalid {field} field for {context}"])
    if len(value) != len(set(value)):
        raise SkeletonError([f"the skeleton probe emitted duplicate {field} entries for {context}"])


def _validate_semantic_material(
    semantic: str, *, context: str, kind: str | None = None
) -> None:
    try:
        payload = json.loads(semantic)
    except (json.JSONDecodeError, RecursionError) as exc:
        raise SkeletonError([f"invalid elaborated semantic material for {context}"]) from exc
    if not isinstance(payload, dict) or payload.keys() != {"generated", "root"}:
        raise SkeletonError([f"invalid elaborated semantic material for {context}"])
    expected = _semantic_keys_for_kind(kind) if kind is not None else None
    _validate_semantic_payload(payload["root"], context=context, expected=expected)
    generated = payload["generated"]
    if not isinstance(generated, list):
        raise SkeletonError([f"invalid elaborated semantic material for {context}"])
    names: list[str] = []
    for entry in generated:
        if (
            not isinstance(entry, dict)
            or entry.keys() != {"material", "name"}
            or not _valid_semantic_name(entry["name"])
        ):
            raise SkeletonError([f"invalid elaborated semantic material for {context}"])
        names.append(json.dumps(entry["name"], sort_keys=True, separators=(",", ":")))
        _validate_semantic_payload(entry["material"], context=context, expected=None)
    if len(names) != len(set(names)):
        raise SkeletonError([f"invalid elaborated semantic material for {context}"])


def _valid_semantic_name(value: object) -> bool:
    depth = 0
    while value is not None:
        if not isinstance(value, dict) or len(value) != 1:
            return False
        if "str" in value:
            pair = value["str"]
            if (
                not isinstance(pair, list)
                or len(pair) != 2
                or not isinstance(pair[1], str)
            ):
                return False
        elif "num" in value:
            pair = value["num"]
            if (
                not isinstance(pair, list)
                or len(pair) != 2
                or type(pair[1]) is not int
                or pair[1] < 0
            ):
                return False
        else:
            return False
        value = pair[0]
        depth += 1
        if depth > 256:
            return False
    return True


def _semantic_keys_for_kind(kind: str) -> set[str]:
    return {
        "def": {"type", "value"},
        "instance": {"type", "value"},
        "opaque": {"type", "value"},
        "class": {"type", "constructors"},
        "inductive": {"type", "constructors"},
        "structure": {"type", "constructors"},
    }.get(kind, {"type"})


def _validate_semantic_payload(
    payload: object, *, context: str, expected: set[str] | None
) -> None:
    allowed = ({"type"}, {"type", "value"}, {"type", "constructors"})
    if not isinstance(payload, dict) or (
        expected is not None and payload.keys() != expected
    ) or (expected is None and set(payload) not in allowed):
        raise SkeletonError([f"invalid elaborated semantic material for {context}"])


def _semantic_pairs(value: object) -> tuple[tuple[str, str], ...]:
    if not isinstance(value, list):
        raise SkeletonError(["invalid semantic identities in skeleton report"])
    pairs: list[tuple[str, str]] = []
    for item in value:
        if (
            not isinstance(item, list)
            or len(item) != 2
            or not all(isinstance(part, str) and part for part in item)
        ):
            raise SkeletonError(["invalid semantic identities in skeleton report"])
        _validate_semantic_material(item[1], context=item[0])
        pairs.append((item[0], item[1]))
    if len({name for name, _ in pairs}) != len(pairs):
        raise SkeletonError(["duplicate semantic identities in skeleton report"])
    return tuple(pairs)


def _require_semantic_pairs(
    value: object,
    *,
    names: object,
    field: str,
    context: str,
) -> None:
    try:
        pairs = _semantic_pairs(value)
    except SkeletonError as exc:
        raise SkeletonError(
            [f"the skeleton probe emitted an invalid {field} field for {context}"]
        ) from exc
    pair_names = [name for name, _ in pairs]
    matches = isinstance(names, list) and pair_names == names
    if not matches:
        raise SkeletonError(
            [f"the skeleton probe emitted mismatched {field} entries for {context}"]
        )


def _module_file_entries(value: object, *, context: str) -> tuple[tuple[str, str, str], ...]:
    if not isinstance(value, list):
        raise SkeletonError([f"invalid assumed module files for {context}"])
    entries: list[tuple[str, str, str]] = []
    for item in value:
        if (
            not isinstance(item, list)
            or len(item) != 3
            or not all(isinstance(part, str) and part for part in item)
            or item[1] != "olean"
        ):
            raise SkeletonError([f"invalid assumed module files for {context}"])
        entries.append((item[0], item[1], item[2]))
    if len({module for module, _, _ in entries}) != len(entries):
        raise SkeletonError([f"duplicate assumed module files for {context}"])
    return tuple(entries)


def _require_module_files(value: object, *, context: str) -> tuple[tuple[str, str, str], ...]:
    return _module_file_entries(value, context=context)


def _hash_module_files(
    value: object,
    *,
    lean_root: Path,
    cache: dict[tuple[str, str], str],
    snapshot_started_ns: int | None = None,
) -> tuple[tuple[str, str, str], ...]:
    identities: list[tuple[str, str, str]] = []
    for module, file_kind, raw_path in _module_file_entries(value, context="probe output"):
        path = Path(raw_path)
        if not path.is_absolute():
            path = lean_root / path
        try:
            resolved = path.resolve(strict=True)
            key = (file_kind, str(resolved))
            digest = cache.get(key)
            if digest is None:
                before = resolved.stat()
                content = resolved.read_bytes()
                after = resolved.stat()
                identity_before = (
                    before.st_dev,
                    before.st_ino,
                    before.st_size,
                    before.st_mtime_ns,
                    before.st_ctime_ns,
                )
                identity_after = (
                    after.st_dev,
                    after.st_ino,
                    after.st_size,
                    after.st_mtime_ns,
                    after.st_ctime_ns,
                )
                if identity_before != identity_after or (
                    snapshot_started_ns is not None
                    and max(after.st_mtime_ns, after.st_ctime_ns) > snapshot_started_ns
                ):
                    raise SkeletonError(
                        [f"assumed module {module} changed during skeleton extraction; retry after the build is idle"]
                    )
                digest = _sha256_id(file_kind.encode("utf-8") + b"\0" + content)
                cache[key] = digest
        except SkeletonError:
            raise
        except (OSError, RuntimeError) as exc:
            raise SkeletonError([f"cannot bind assumed module {module} to {file_kind} file {path}: {exc}"]) from exc
        identities.append((module, file_kind, digest))
    return tuple(identities)


# --------------------------------------------------------------------------- #
# Extraction
# --------------------------------------------------------------------------- #


def extract_skeletons(
    blueprint_dir: str | Path,
    *,
    lean_root: str | Path,
    runner: ProbeRunner | None = None,
    node_ids: tuple[str, ...] | None = None,
) -> SkeletonReport:
    """Extract the skeleton of every ``lean:`` declaration the blueprint names.

    ``runner`` executes the rendered probe and returns Lean's standard output.
    A declaration the lexical index cannot place is reported as unresolved
    without running Lean, exactly as ``autoform check --lean-root`` reports it.
    """

    try:
        graph = load_graph(blueprint_dir)
    except GraphValidationError as exc:
        raise SkeletonError(exc.issues) from exc
    root = Path(lean_root).expanduser().resolve()
    graph_snapshot = _graph_snapshot(graph)
    control_snapshot = _project_control_snapshot(root)
    libraries = lean_libraries(root)
    if _project_control_snapshot(root) != control_snapshot:
        raise SkeletonError(
            ["Lean project configuration changed while skeletons were being extracted; retry after the project is idle"]
        )
    index = index_project(root)
    report = extract_graph_skeletons(
        graph,
        lean_root=root,
        libraries=libraries,
        index=index,
        runner=runner or run_probe,
        node_ids=node_ids,
    )
    if index_project(root).source_digest != index.source_digest:
        raise SkeletonError(["Lean sources changed while skeletons were being extracted; retry after the build is idle"])
    if _project_control_snapshot(root) != control_snapshot:
        raise SkeletonError(
            ["Lean project configuration changed while skeletons were being extracted; retry after the project is idle"]
        )
    try:
        current_graph = load_graph(graph.blueprint_dir)
    except GraphValidationError as exc:
        raise SkeletonError(
            ["the blueprint changed while skeletons were being extracted; retry after the project is idle"]
        ) from exc
    if _graph_snapshot(current_graph) != graph_snapshot:
        raise SkeletonError(
            ["the blueprint changed while skeletons were being extracted; retry after the project is idle"]
        )
    for node in report.nodes:
        current = current_graph.nodes.get(node.node_id)
        if current is None or source_passage(current, current_graph.blueprint_dir) != (
            node.passage,
            node.passage_locator,
        ):
            raise SkeletonError(
                [f"{node.node_id}: source passage changed while skeletons were being extracted; retry after the project is idle"]
            )
    return report


def extract_graph_skeletons(
    graph: Graph,
    *,
    lean_root: Path,
    libraries: tuple[LeanLibrary, ...],
    index: SourceIndex,
    runner: ProbeRunner,
    node_ids: tuple[str, ...] | None = None,
) -> SkeletonReport:
    """Extract skeletons for an already loaded graph."""

    selected = [graph.nodes[node_id] for node_id in sorted(graph.nodes) if graph.nodes[node_id].lean]
    if node_ids is not None:
        wanted = set(node_ids)
        unknown = sorted(wanted - set(graph.nodes))
        if unknown:
            raise SkeletonError([f"unknown article: {node_id}" for node_id in unknown])
        selected = [node for node in selected if node.id in wanted]
    passages = {node.id: source_passage(node, graph.blueprint_dir) for node in selected}

    unresolved: list[str] = []
    imports: set[str] = set()
    roots: list[str] = []
    for node in selected:
        for name in declaration_names(node.lean or ""):
            location = index.find(name)
            module = None if location is None else module_of(lean_root / location.path, libraries)
            if location is None:
                unresolved.append(f"{node.id}: declaration not found in the Lean sources: {name}")
                continue
            if module is None:
                unresolved.append(f"{node.id}: {name} is in {location.path.as_posix()}, which no library target builds")
                continue
            imports.add(module)
            if name not in roots:
                roots.append(name)

    records: dict[str, dict[str, object]] = {}
    snapshot_started_ns: int | None = None
    if roots:
        program = render_probe(
            imports=tuple(sorted(imports)),
            roots=tuple(roots),
            project_roots=tuple(root for library in libraries for root in library.roots),
        )
        snapshot_started_ns = time.time_ns()
        records = parse_probe_output(runner(program, lean_root), expected_roots=tuple(roots))

    nodes: list[NodeSkeleton] = []
    module_hashes: dict[tuple[str, str], str] = {}
    for node in selected:
        declarations: list[DeclarationSkeleton] = []
        for name in declaration_names(node.lean or ""):
            if name not in roots:
                continue
            record = records.get(name)
            if record is None:
                unresolved.append(f"{node.id}: the probe returned nothing for {name}")
                continue
            if not record.get("found"):
                unresolved.append(f"{node.id}: {name} is not in the built environment; run `lake build`")
                continue
            declarations.append(
                _declaration(
                    record,
                    libraries=libraries,
                    lean_root=lean_root,
                    index=index,
                    module_hashes=module_hashes,
                    snapshot_started_ns=snapshot_started_ns,
                )
            )
        passage, locator = passages[node.id]
        nodes.append(
            NodeSkeleton(
                node_id=node.id,
                article_path=_article_path(node, graph),
                declarations=tuple(declarations),
                passage=passage,
                passage_locator=locator,
            )
        )
    return SkeletonReport(nodes=tuple(nodes), unresolved=tuple(sorted(set(unresolved))))


_TRAILING_VALUE = re.compile(r"(?::=\s*(?:by)?|\bwhere)\s*\Z")
_LINE_LOCATOR = re.compile(r"\AL(\d+)(?:-L(\d+))?\Z")


def _statement(value: object) -> str | None:
    """Normalize the parser's cut: drop a trailing `:=`, `:= by`, or `where`."""

    if not isinstance(value, str) or not value.strip():
        return None
    return _TRAILING_VALUE.sub("", value).rstrip()


def source_passage(node: Node, blueprint: Path) -> tuple[str | None, str | None]:
    """Return the passage an article cites through a line locator, and the locator.

    A ``## Sources`` link to a non-Markdown file inside the blueprint with a
    ``#L<start>-L<end>`` fragment names the exact source text the statement
    came from. The first such link wins. Markdown targets are notes, not
    passages, and are ignored here.
    """

    for target in node.sources:
        path, _, fragment = target.partition("#")
        match = _LINE_LOCATOR.fullmatch(fragment or "")
        if match is None or not path or path.endswith(".md"):
            continue
        candidate = (node.path.parent / path).resolve()
        try:
            candidate.relative_to(blueprint.resolve())
            captured = _read_snapshot_file(candidate)
            if captured is None:
                continue
            # Lines are what an editor or `sed` counts: newline-separated. Python's
            # `splitlines` also breaks on form feeds, which `pdftotext` writes
            # between pages, and every locator into such a file would then drift
            # by one line per page.
            lines = captured[0].decode("utf-8").split("\n")
        except (ValueError, UnicodeError):
            continue
        start = int(match.group(1))
        end = int(match.group(2) or start)
        if start < 1 or end < start or end > len(lines):
            continue
        relative = candidate.relative_to(blueprint.resolve()).as_posix()
        return "\n".join(lines[start - 1 : end]), f"{relative}#L{start}-L{end}"
    return None, None


def _article_path(node: Node, graph: Graph) -> str:
    try:
        return node.path.relative_to(graph.blueprint_dir).as_posix()
    except ValueError:
        return node.path.name


def _declaration(
    record: dict[str, object],
    *,
    libraries: tuple[LeanLibrary, ...],
    lean_root: Path,
    index: SourceIndex,
    module_hashes: dict[tuple[str, str], str],
    snapshot_started_ns: int | None,
) -> DeclarationSkeleton:
    trusted_records = record.get("trusted")
    trusted = [
        _trusted(item, libraries=libraries, lean_root=lean_root, index=index)
        for item in (trusted_records if isinstance(trusted_records, list) else [])
        if isinstance(item, dict)
    ]
    name = str(record["root"])
    module = str(record.get("module") or "")
    start, end = _range(record.get("range"))
    declaration = DeclarationSkeleton(
        name=name,
        kind=str(record.get("kind") or "unknown"),
        module=module,
        path=_source_path(name, module, libraries=libraries, lean_root=lean_root, index=index),
        start_line=start,
        end_line=end,
        signature=str(record.get("signature") or ""),
        semantic=str(record["semantic"]),
        lean_version=str(record["lean_version"]),
        depends=tuple(_strings(record.get("depends"))),
        trusted=tuple(_dependency_order(trusted)),
        assumed=tuple(_strings(record.get("assumed"))),
        assumed_semantics=_semantic_pairs(record.get("assumed_semantics")),
        boundary_modules=_hash_module_files(
            record.get("boundary_modules"),
            lean_root=lean_root,
            cache=module_hashes,
            snapshot_started_ns=snapshot_started_ns,
        ),
        axioms=tuple(_strings(record.get("axioms"))),
        axiom_semantics=_semantic_pairs(record.get("axiom_semantics")),
        source=_optional_probe_string(record.get("source")),
        statement=_statement(record.get("statement_source")),
    )
    return declaration


def _trusted(
    item: dict[str, object],
    *,
    libraries: tuple[LeanLibrary, ...],
    lean_root: Path,
    index: SourceIndex,
) -> TrustedDeclaration:
    name = str(item.get("name") or "")
    module = str(item.get("module") or "")
    start, end = _range(item.get("range"))
    trusted = TrustedDeclaration(
        name=name,
        kind=str(item.get("kind") or "unknown"),
        module=module,
        path=_source_path(name, module, libraries=libraries, lean_root=lean_root, index=index),
        start_line=start,
        end_line=end,
        signature=str(item.get("signature") or ""),
        semantic=str(item["semantic"]),
        depends=tuple(_strings(item.get("depends"))),
        source=_optional_probe_string(item.get("source")),
    )
    return trusted


def _optional_probe_string(value: object) -> str | None:
    return value if isinstance(value, str) else None


def _source_path(
    name: str,
    module: str,
    *,
    libraries: tuple[LeanLibrary, ...],
    lean_root: Path,
    index: SourceIndex,
) -> str | None:
    # The module name is authoritative: it is what Lean compiled. The lexical
    # index is only a fallback for a module whose file the library layout
    # cannot place.
    path = path_of(module, libraries, lean_root) if module else None
    if path is not None:
        return path
    location = index.find(name)
    return None if location is None else location.path.as_posix()


def _range(value: object) -> tuple[int | None, int | None]:
    if isinstance(value, list) and len(value) == 2 and all(isinstance(item, int) for item in value):
        return value[0], value[1]
    return None, None


def _strings(value: object) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(item) for item in value]


def _dependency_order(items: list[TrustedDeclaration]) -> list[TrustedDeclaration]:
    """Order trusted declarations so each is read after what it rests on.

    Ties are broken by name, so the order is a function of the sources alone.
    """

    by_name = {item.name: item for item in items}
    order: list[TrustedDeclaration] = []
    done: set[str] = set()
    visiting: set[str] = set()

    def visit(name: str) -> None:
        if name in done or name in visiting or name not in by_name:
            return
        visiting.add(name)
        for dependency in sorted(by_name[name].depends):
            visit(dependency)
        visiting.discard(name)
        done.add(name)
        order.append(by_name[name])

    for name in sorted(by_name):
        visit(name)
    return order


# --------------------------------------------------------------------------- #
# Presentation
# --------------------------------------------------------------------------- #


def source_excerpt(item: TrustedDeclaration | DeclarationSkeleton, lean_root: Path) -> str | None:
    """Return the source lines of ``item``, or ``None`` when they cannot be read."""

    if item.path is None or item.start_line is None or item.end_line is None:
        return None
    root = lean_root.resolve()
    candidate = (root / item.path).resolve()
    try:
        candidate.relative_to(root)
        lines = candidate.read_text(encoding="utf-8").split("\n")
    except (ValueError, OSError, UnicodeError):
        return None
    if item.start_line < 1 or item.end_line > len(lines) or item.end_line < item.start_line:
        return None
    return "\n".join(lines[item.start_line - 1 : item.end_line])


def format_report(report: SkeletonReport, *, lean_root: Path | None = None) -> str:
    """Render the report as the text a reviewer reads.

    Source excerpts captured by the probe travel inside the report. The
    ``lean_root`` argument remains for call compatibility and is never reread.
    """

    out: list[str] = []
    for node in report.nodes:
        if len(node.declarations) > 1:
            out.append(f"## {node.node_id} · article skeleton {node.hash}")
            out.append("")
        for declaration in node.declarations:
            out.append(f"== {node.node_id} · {declaration.kind} {declaration.name}")
            out.extend(f"   {line}" for line in declaration.signature.splitlines())
            if declaration.source is not None:
                out.extend(f"   {line}" for line in declaration.source.splitlines())
            elif declaration.statement is not None:
                out.append("   -- as written:")
                out.extend(f"   {line}" for line in declaration.statement.splitlines())
            out.append("")
            out.append(f"   {_trust_summary(declaration)} · skeleton {declaration.hash}")
            if declaration.assumed:
                out.append(f"   assumes: {', '.join(declaration.assumed)}")
            out.append(f"   axioms: {', '.join(declaration.axioms) if declaration.axioms else 'none'}")
            for item in declaration.trusted:
                out.append("")
                out.append(f"   -- {item.kind} {item.name}  ({_where(item)})")
                out.extend(f"   -- {line}" for line in item.signature.splitlines())
                excerpt = item.source
                if excerpt is None:
                    out.extend(f"   {line}" for line in item.signature.splitlines())
                else:
                    out.extend(f"   {line}" for line in excerpt.splitlines())
            out.append("")
        if not node.declarations:
            out.append(f"== {node.node_id} · no skeleton")
            out.append("")
    for issue in report.unresolved:
        out.append(f"error: {issue}")
    return "\n".join(out).rstrip("\n") + "\n"


PACKET_MANIFEST = "manifest.json"
#: The joint packet of an article's declarations, what a faithfulness judge reads.
ARTICLE_PACKET = "article.lean"
_PACKET_SCHEMA = "autoform-skeleton-packets/v1"
_PASSAGE_SCHEMA = "autoform-skeleton-passages/v1"


def _output_identity(path: Path) -> tuple[int, int, str] | None:
    """Return the identity of an output path without following its final link."""

    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise SkeletonError([f"cannot inspect skeleton output {path}: {exc}"]) from exc
    if path.is_symlink():
        raise SkeletonError([f"refusing symlink packet output: {path}"])
    digest = hashlib.sha256()
    if path.is_file():
        try:
            digest.update(b"file\0")
            digest.update(path.read_bytes())
        except OSError as exc:
            raise SkeletonError([f"cannot inspect skeleton output {path}: {exc}"]) from exc
        return metadata.st_dev, metadata.st_ino, digest.hexdigest()
    if not path.is_dir():
        raise SkeletonError([f"skeleton output is not a regular file or directory: {path}"])
    digest.update(b"directory\0")
    try:
        for child in sorted(path.rglob("*"), key=lambda candidate: candidate.relative_to(path).as_posix()):
            relative = child.relative_to(path).as_posix()
            if child.is_symlink():
                raise SkeletonError([f"refusing symlink packet output: {child}"])
            digest.update(relative.encode("utf-8"))
            digest.update(b"\0")
            if child.is_dir():
                digest.update(b"directory\0")
            elif child.is_file():
                digest.update(b"file\0")
                digest.update(child.read_bytes())
                digest.update(b"\0")
            else:
                raise SkeletonError([f"refusing special file in packet output: {child}"])
    except OSError as exc:
        raise SkeletonError([f"cannot inspect skeleton output {path}: {exc}"]) from exc
    return metadata.st_dev, metadata.st_ino, digest.hexdigest()


def _validate_managed_output(path: Path, *, kind: str) -> tuple[int, int, str] | None:
    identity = _output_identity(path)
    if identity is None:
        return identity
    if not path.is_dir():
        raise SkeletonError([f"packet output exists and is not a directory: {path}"])
    try:
        if not any(path.iterdir()):
            return identity
    except OSError as exc:
        raise SkeletonError([f"cannot inspect skeleton output {path}: {exc}"]) from exc
    manifest = path / PACKET_MANIFEST
    if manifest.is_symlink() or not manifest.is_file():
        raise SkeletonError([f"refusing to overwrite non-Autoform packet output: {path}"])
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise SkeletonError([f"refusing to overwrite non-Autoform packet output: {path}"]) from exc
    if not isinstance(payload, dict):
        raise SkeletonError([f"refusing to overwrite non-Autoform packet output: {path}"])
    expected_schema = _PACKET_SCHEMA if kind == "packets" else _PASSAGE_SCHEMA
    entries = payload.get(kind)
    if (
        payload.get("kind") != kind
        or payload.get("schema") != expected_schema
        or not isinstance(entries, list)
    ):
        raise SkeletonError([f"refusing to overwrite non-Autoform packet output: {path}"])
    return identity


def _safe_node_path(node_id: str) -> Path:
    path = Path(*node_id.split("/"))
    if (
        not node_id
        or path.is_absolute()
        or path.as_posix() != node_id
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise SkeletonError([f"unsafe article id in packet output: {node_id!r}"])
    return path


def _packet_filename(name: str) -> str:
    pieces: list[str] = []
    for character in name:
        if character.isascii() and (character.isalnum() or character in {".", "_", "-"}):
            pieces.append(character)
        else:
            pieces.extend(f"%{byte:02X}" for byte in character.encode("utf-8"))
    encoded = "".join(pieces)
    digest = hashlib.sha256(name.encode("utf-8")).hexdigest()
    if not encoded or len(os.fsencode(encoded)) > 180:
        encoded = "declaration"
    return f"{encoded}--{digest}.lean"


def _stage_output(destination: Path) -> Path:
    destination.parent.mkdir(parents=True, exist_ok=True)
    existing_mode: int | None = None
    try:
        if not destination.is_symlink() and destination.is_dir():
            existing_mode = destination.stat().st_mode & 0o7777
    except OSError as exc:
        raise SkeletonError([f"cannot inspect skeleton output {destination}: {exc}"]) from exc
    for _ in range(100):
        stage = destination.with_name(
            f".{destination.name}.autoform-stage-{secrets.token_hex(8)}"
        )
        try:
            stage.mkdir()
        except FileExistsError:
            continue
        try:
            if existing_mode is not None:
                stage.chmod(existing_mode)
        except OSError:
            shutil.rmtree(stage, ignore_errors=True)
            raise
        return stage
    raise SkeletonError([f"cannot allocate staging directory beside {destination}"])


def _stage_report_output(
    report: SkeletonReport,
    destination: Path,
) -> tuple[Path, tuple[int, int, str] | None]:
    """Write a report to a same-directory stage and capture the old identity."""

    identity = _output_identity(destination)
    existing_mode: int | None = None
    if identity is not None:
        if not destination.is_file():
            raise SkeletonError([f"report output exists and is not a regular file: {destination}"])
        existing_mode = destination.stat().st_mode & 0o7777
    destination.parent.mkdir(parents=True, exist_ok=True)
    for _ in range(100):
        stage = destination.with_name(
            f".{destination.name}.autoform-stage-{secrets.token_hex(8)}"
        )
        try:
            with stage.open("x", encoding="utf-8") as stream:
                stream.write(report.to_json() + "\n")
                stream.flush()
                os.fsync(stream.fileno())
            if existing_mode is not None:
                stage.chmod(existing_mode)
        except FileExistsError:
            continue
        except BaseException:
            stage.unlink(missing_ok=True)
            raise
        return stage, identity
    raise SkeletonError([f"cannot allocate staging file beside {destination}"])


def _remove_output(path: Path) -> None:
    """Remove one transaction-owned file or directory without following links."""

    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return
    if stat.S_ISDIR(metadata.st_mode):
        shutil.rmtree(path)
    else:
        path.unlink()


def _rename_no_replace(source: Path, destination: Path) -> None:
    """Atomically rename ``source`` only when ``destination`` is absent."""

    if os.name == "nt":  # pragma: no cover - Windows-specific path
        os.rename(source, destination)
        return

    library = ctypes.CDLL(None, use_errno=True)
    source_bytes = os.fsencode(source)
    destination_bytes = os.fsencode(destination)
    if sys.platform.startswith("linux"):
        try:
            rename = library.renameat2
        except AttributeError as exc:
            raise SkeletonError(
                ["atomic no-replace rename is unavailable on this Linux system"]
            ) from exc
        rename.argtypes = (
            ctypes.c_int,
            ctypes.c_char_p,
            ctypes.c_int,
            ctypes.c_char_p,
            ctypes.c_uint,
        )
        rename.restype = ctypes.c_int
        result = rename(-100, source_bytes, -100, destination_bytes, 1)
    elif sys.platform == "darwin":
        try:
            rename = library.renamex_np
        except AttributeError as exc:
            raise SkeletonError(
                ["atomic no-replace rename is unavailable on this macOS system"]
            ) from exc
        rename.argtypes = (ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint)
        rename.restype = ctypes.c_int
        result = rename(source_bytes, destination_bytes, 0x00000004)
    else:
        raise SkeletonError(
            [f"atomic no-replace rename is unsupported on {sys.platform}"]
        )
    if result != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), destination)


def _install_output(stage: Path, destination: Path) -> None:
    """Install a stage without overwriting a concurrent output."""

    metadata = stage.lstat()
    if stat.S_ISREG(metadata.st_mode):
        os.link(stage, destination)
        stage.unlink()
    else:
        _rename_no_replace(stage, destination)


def _preflight_output_installs(
    outputs: list[tuple[Path, Path, tuple[int, int, str] | None]],
) -> None:
    """Prove each destination filesystem supports its artifact install."""

    checked: set[tuple[int, int]] = set()
    for destination, stage, _ in outputs:
        try:
            stage_metadata = stage.lstat()
            device = destination.parent.stat().st_dev
        except OSError as exc:
            raise SkeletonError([f"cannot inspect skeleton output stage {stage}: {exc}"]) from exc
        artifact_kind = stat.S_IFMT(stage_metadata.st_mode)
        if artifact_kind not in {stat.S_IFREG, stat.S_IFDIR}:
            raise SkeletonError([f"skeleton output stage is not a file or directory: {stage}"])
        key = (device, artifact_kind)
        if key in checked:
            continue
        checked.add(key)
        probe_root = Path(
            tempfile.mkdtemp(
                prefix=f".{destination.name}.autoform-preflight-",
                dir=destination.parent,
            )
        )
        source = probe_root / "source"
        target = probe_root / "target"
        try:
            if artifact_kind == stat.S_IFREG:
                source.touch(exist_ok=False)
            else:
                source.mkdir()
            _install_output(source, target)
        except BaseException:
            try:
                _remove_output(probe_root)
            except OSError as cleanup_exc:
                warnings.warn(
                    f"could not remove output preflight artifacts at {probe_root}: {cleanup_exc}",
                    RuntimeWarning,
                    stacklevel=2,
                )
            raise
        try:
            _remove_output(probe_root)
        except OSError as cleanup_exc:
            raise SkeletonError(
                [f"could not remove output preflight artifacts at {probe_root}: {cleanup_exc}"]
            ) from cleanup_exc


def _replace_outputs(
    outputs: list[tuple[Path, Path, tuple[int, int, str] | None]],
) -> None:
    """Commit staged outputs with rollback, but not cross-path linearizability.

    Each rename is atomic. Readers can still observe the interval between the
    renames; avoiding that requires one shared generation pointer rather than
    another rollback branch.
    """

    _preflight_output_installs(outputs)
    for destination, _, identity in outputs:
        if _output_identity(destination) != identity:
            raise SkeletonError([f"packet output changed during publication: {destination}"])
    backups: dict[Path, tuple[Path, tuple[int, int, str]]] = {}
    installs: dict[Path, tuple[Path, tuple[int, int, str]]] = {}
    try:
        for destination, _, identity in outputs:
            if identity is None:
                continue
            backup = destination.with_name(
                f".{destination.name}.autoform-backup-{secrets.token_hex(8)}"
            )
            backups[destination] = (backup, identity)
            os.replace(destination, backup)
            if _output_identity(backup) != identity:
                raise SkeletonError([f"packet output changed during publication: {destination}"])
        for destination, stage, _ in outputs:
            stage_identity = _output_identity(stage)
            if stage_identity is None:
                raise SkeletonError([f"skeleton output stage disappeared: {stage}"])
            installs[destination] = (stage, stage_identity)
            _install_output(stage, destination)
    except BaseException as exc:
        conflicts: set[Path] = set()
        rollback_issues: list[str] = []
        for destination, (stage, expected) in reversed(installs.items()):
            try:
                stage_identity = _output_identity(stage)
                destination_identity = _output_identity(destination)
                if stage_identity == expected and destination_identity is None:
                    continue
                if destination_identity != expected:
                    if destination_identity is None:
                        continue
                    conflicts.add(destination)
                    rollback_issues.append(
                        f"published output changed during rollback and was preserved at {destination}"
                    )
                    continue
                quarantine = destination.with_name(
                    f".{destination.name}.autoform-rollback-{secrets.token_hex(8)}"
                )
                os.replace(destination, quarantine)
                try:
                    quarantine_identity = _output_identity(quarantine)
                    if quarantine_identity != expected:
                        rollback_issues.append(
                            f"changed rolled-back output was preserved for recovery at {quarantine}"
                        )
                        continue
                    _remove_output(quarantine)
                except (OSError, SkeletonError) as cleanup_exc:
                    rollback_issues.append(
                        f"could not remove rolled-back output preserved for recovery at {quarantine}: {cleanup_exc}"
                    )
            except (OSError, SkeletonError) as rollback_exc:
                if _output_identity(destination) is not None:
                    conflicts.add(destination)
                rollback_issues.append(
                    f"could not roll back skeleton output {destination}: {rollback_exc}"
                )
        for destination, (backup, expected) in backups.items():
            if destination in conflicts:
                rollback_issues.append(f"previous output was preserved for recovery at {backup}")
                continue
            try:
                backup_identity = _output_identity(backup)
                destination_identity = _output_identity(destination)
                if backup_identity is not None and destination_identity is None:
                    _install_output(backup, destination)
                elif backup_identity == expected:
                    rollback_issues.append(f"previous output was preserved for recovery at {backup}")
                elif backup_identity is None and destination_identity == expected:
                    continue
                elif backup_identity is not None:
                    rollback_issues.append(f"changed backup was preserved for recovery at {backup}")
                else:
                    rollback_issues.append(
                        f"could not find previous skeleton output for {destination} during rollback"
                    )
            except (OSError, SkeletonError) as rollback_exc:
                rollback_issues.append(
                    f"could not restore skeleton output {destination}; previous output remains at {backup}: {rollback_exc}"
                )
        if not isinstance(exc, (OSError, SkeletonError)):
            raise
        issues = list(exc.issues) if isinstance(exc, SkeletonError) else [f"could not publish skeleton output: {exc}"]
        raise SkeletonError([*issues, *rollback_issues]) from exc
    for backup, expected in backups.values():
        try:
            backup_identity = _output_identity(backup)
            if backup_identity is None:
                warnings.warn(
                    f"skeleton output backup disappeared before cleanup: {backup}",
                    RuntimeWarning,
                    stacklevel=2,
                )
                continue
            if backup_identity != expected:
                warnings.warn(
                    f"skeleton output backup changed before cleanup and was preserved at {backup}",
                    RuntimeWarning,
                    stacklevel=2,
                )
                continue
            _remove_output(backup)
        except (OSError, SkeletonError) as cleanup_exc:
            warnings.warn(
                f"could not remove previous skeleton output preserved at {backup}: {cleanup_exc}",
                RuntimeWarning,
                stacklevel=2,
            )


def _paths_overlap(first: Path, second: Path) -> bool:
    first_resolved = first.resolve()
    second_resolved = second.resolve()
    return (
        first_resolved == second_resolved
        or first_resolved in second_resolved.parents
        or second_resolved in first_resolved.parents
    )


def write_skeleton_report(report: SkeletonReport, destination: str | Path) -> Path:
    """Failure-atomically replace one JSON skeleton report."""

    requested = Path(destination).expanduser()
    if requested.is_symlink():
        raise SkeletonError([f"refusing symlink report output: {requested}"])
    output = Path(os.path.abspath(requested))
    stage: Path | None = None
    try:
        stage, identity = _stage_report_output(report, output)
        _replace_outputs([(output, stage, identity)])
        stage = None
    except OSError as exc:
        raise SkeletonError([f"could not prepare skeleton report output: {exc}"]) from exc
    finally:
        if stage is not None:
            try:
                _remove_output(stage)
            except OSError:
                pass
    return output


def write_packets(
    report: SkeletonReport,
    directory: str | Path,
    *,
    passages: str | Path | None = None,
    report_path: str | Path | None = None,
) -> list[Path]:
    """Write one blind packet per skeleton for independent auditors.

    Each packet holds only what the auditor may see: the comment-stripped
    skeleton. Nothing names the article, the source, or the intent. The
    manifest beside the packets maps each file back to its article and hash so
    testimony about a packet can be filed and checked, without the auditor
    reading it.

    With ``passages``, the source passage each article cites is written to a
    second directory, one ``passage.txt`` per article. A faithfulness judge
    gets a packet and its passage; an auditor of one declaration gets the
    packet alone, which is why the two never share a directory.

    With ``report_path``, the JSON report joins the same failure-atomic
    publication transaction.
    """

    if not report.clean:
        raise SkeletonError(
            ["refusing to publish review packets from an incomplete skeleton report"]
        )

    requested_root = Path(directory).expanduser()
    if requested_root.is_symlink():
        raise SkeletonError([f"refusing symlink packet output: {requested_root}"])
    root = Path(os.path.abspath(requested_root))
    requested_passages = Path(passages).expanduser() if passages is not None else None
    if requested_passages is not None and requested_passages.is_symlink():
        raise SkeletonError([f"refusing symlink packet output: {requested_passages}"])
    passages_root = (
        Path(os.path.abspath(requested_passages)) if requested_passages is not None else None
    )
    if passages_root is not None and _paths_overlap(root, passages_root):
        raise SkeletonError(["packet and passage output directories must be disjoint"])
    requested_report = Path(report_path).expanduser() if report_path is not None else None
    if requested_report is not None and requested_report.is_symlink():
        raise SkeletonError([f"refusing symlink report output: {requested_report}"])
    report_destination = (
        Path(os.path.abspath(requested_report)) if requested_report is not None else None
    )
    if report_destination is not None and (
        _paths_overlap(root, report_destination)
        or (passages_root is not None and _paths_overlap(passages_root, report_destination))
    ):
        raise SkeletonError(["report output must be disjoint from packet and passage directories"])
    root_identity = _validate_managed_output(root, kind="packets")
    passages_identity = (
        _validate_managed_output(passages_root, kind="passages")
        if passages_root is not None
        else None
    )
    packet_stage: Path | None = None
    passages_stage: Path | None = None
    report_stage: Path | None = None
    report_identity: tuple[int, int, str] | None = None
    written: list[Path] = []
    manifest: list[dict[str, str]] = []
    passage_manifest: list[dict[str, str]] = []
    try:
        packet_stage = _stage_output(root)
        passages_stage = _stage_output(passages_root) if passages_root is not None else None
        if report_destination is not None:
            report_stage, report_identity = _stage_report_output(report, report_destination)
        for node in report.nodes:
            node_path = _safe_node_path(node.node_id)
            passage_path: str | None = None
            if passages_stage is not None and node.passage is not None:
                passage_relative = node_path / "passage.txt"
                target = passages_stage / passage_relative
                target.parent.mkdir(parents=True, exist_ok=True)
                passage_bytes = (node.passage + "\n").encode("utf-8")
                target.write_bytes(passage_bytes)
                passage_path = passage_relative.as_posix()
                passage_manifest.append(
                    {
                        "hash": _sha256_id(passage_bytes),
                        "node_id": node.node_id,
                        "passage": passage_path,
                        "review_hash": node.review_hash,
                    }
                )
            if node.declarations:
                article_relative = node_path / ARTICLE_PACKET
                article = packet_stage / article_relative
                article.parent.mkdir(parents=True, exist_ok=True)
                article.write_text(node.blind_text(), encoding="utf-8")
                written.append(root / article_relative)
            for declaration in node.declarations:
                relative = node_path / _packet_filename(declaration.name)
                path = packet_stage / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(declaration.blind_text(), encoding="utf-8")
                written.append(root / relative)
                entry = {
                    "article_packet": (node_path / ARTICLE_PACKET).as_posix(),
                    "article_packet_hash": node.evidence_hash,
                    "declaration": declaration.name,
                    "hash": declaration.hash,
                    "node_id": node.node_id,
                    "packet": relative.as_posix(),
                    "packet_hash": declaration.evidence_hash,
                    "review_hash": node.review_hash,
                }
                if passage_path is not None:
                    entry["passage"] = passage_path
                    entry["passage_locator"] = node.passage_locator or ""
                manifest.append(entry)
        (packet_stage / PACKET_MANIFEST).write_text(
            json.dumps(
                {"kind": "packets", "packets": manifest, "schema": _PACKET_SCHEMA},
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        if passages_stage is not None:
            (passages_stage / PACKET_MANIFEST).write_text(
                json.dumps(
                    {
                        "kind": "passages",
                        "passages": passage_manifest,
                        "schema": _PASSAGE_SCHEMA,
                    },
                    indent=2,
                    sort_keys=True,
                )
                + "\n",
                encoding="utf-8",
            )
        outputs = [(root, packet_stage, root_identity)]
        if passages_root is not None and passages_stage is not None:
            outputs.append((passages_root, passages_stage, passages_identity))
        if report_destination is not None and report_stage is not None:
            outputs.append((report_destination, report_stage, report_identity))
        _replace_outputs(outputs)
        packet_stage = None
        passages_stage = None
        report_stage = None
    except OSError as exc:
        raise SkeletonError([f"could not prepare skeleton output: {exc}"]) from exc
    finally:
        for stage in (packet_stage, passages_stage, report_stage):
            if stage is not None:
                try:
                    _remove_output(stage)
                except OSError:
                    pass
    return written


def _trust_summary(declaration: DeclarationSkeleton) -> str:
    count = len(declaration.trusted)
    noun = "declaration" if count == 1 else "declarations"
    summary = f"trusts {count} local {noun}, {_plural(declaration.skeleton_lines, 'line')} to read"
    if declaration.declaration_lines:
        summary += f"; the declaration itself spans {_plural(declaration.declaration_lines, 'line')}"
    return summary


def _plural(count: int, noun: str) -> str:
    return f"{count} {noun}" if count == 1 else f"{count} {noun}s"


def _where(item: TrustedDeclaration) -> str:
    location = item.path or item.module or "?"
    if item.start_line is not None and item.end_line is not None:
        span = f"{item.start_line}" if item.start_line == item.end_line else f"{item.start_line}-{item.end_line}"
        return f"{location}:{span}"
    return location


__all__ = [
    "ARTICLE_PACKET",
    "DEFAULT_PROBE_TIMEOUT",
    "PROBE_MARKER",
    "SEMANTIC_SCHEMA",
    "SKELETON_SCHEMA",
    "DeclarationSkeleton",
    "LeanLibrary",
    "NodeSkeleton",
    "PACKET_MANIFEST",
    "ProbeRunner",
    "SkeletonError",
    "SkeletonReport",
    "TrustedDeclaration",
    "extract_graph_skeletons",
    "extract_skeletons",
    "format_report",
    "lean_libraries",
    "load_skeleton_report",
    "module_of",
    "parse_probe_output",
    "path_of",
    "render_probe",
    "run_probe",
    "source_excerpt",
    "source_passage",
    "write_packets",
    "write_skeleton_report",
]
