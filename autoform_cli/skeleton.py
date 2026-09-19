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

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path

from .graph import Graph, GraphValidationError, Node, load_graph
from .lean import SourceIndex, declaration_names, index_project, strip_lean_comments

try:  # Python 3.11+
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.10
    import tomli as tomllib  # type: ignore[no-redef]

SKELETON_SCHEMA = "autoform-skeleton/v1"

#: Every line the probe wants read back starts with this marker, so Lean's own
#: informational output can never be mistaken for a result.
PROBE_MARKER = "AUTOFORM_SKELETON "

#: Module roots whose declarations are never listed as assumptions: they are
#: the language itself, not mathematics a reader might want to double-check.
_CORE_MODULE_ROOTS = ("Init", "Lean", "Std", "Lake")

DEFAULT_PROBE_TIMEOUT = 600.0

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
    depends: tuple[str, ...]
    source: str | None = None

    @property
    def lines(self) -> int:
        if self.start_line is None or self.end_line is None:
            return 0
        return self.end_line - self.start_line + 1

    def as_dict(self) -> dict[str, object]:
        return {
            "depends": list(self.depends),
            "end_line": self.end_line,
            "kind": self.kind,
            "module": self.module,
            "name": self.name,
            "path": self.path,
            "signature": self.signature,
            "source": self.source,
            "start_line": self.start_line,
        }


@dataclass(frozen=True, slots=True)
class HypothesisProbe:
    """One attempt to prove a theorem with a hypothesis deleted.

    ``hypothesis`` is ``*`` when every propositional hypothesis was deleted at
    once. ``proved`` is one-sided: true means cheap automation closed the
    weakened statement, which is a finding; false means nothing was learned.
    """

    hypothesis: str
    hypothesis_type: str
    statement: str
    proved: bool
    tactic: str | None

    def as_dict(self) -> dict[str, object]:
        return {
            "hypothesis": self.hypothesis,
            "hypothesis_type": self.hypothesis_type,
            "proved": self.proved,
            "statement": self.statement,
            "tactic": self.tactic,
        }


@dataclass(frozen=True, slots=True)
class DefinitionCheck:
    """One check on a propositional definition: ``always``, ``never``,
    ``unused-argument``, or ``redundant-clause``. ``holds`` true is a finding."""

    kind: str
    detail: str
    holds: bool
    tactic: str | None

    def as_dict(self) -> dict[str, object]:
        return {"detail": self.detail, "holds": self.holds, "kind": self.kind, "tactic": self.tactic}


@dataclass(frozen=True, slots=True)
class Witness:
    """A ``<Def>.witness`` or ``<Def>.counterexample`` declaration, if filed.

    ``status`` is ``found``, ``missing``, ``mismatched`` (wrong shape), or
    ``sorry``. A missing witness is advisory; a filed one that is wrong is not.
    """

    role: str
    name: str
    status: str

    def as_dict(self) -> dict[str, object]:
        return {"name": self.name, "role": self.role, "status": self.status}


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
    trusted: tuple[TrustedDeclaration, ...]
    assumed: tuple[str, ...]
    axioms: tuple[str, ...]
    #: The declaration's own source when it is a definition, whose body is its
    #: meaning. A theorem's source holds its proof, which is never shown.
    source: str | None = None
    #: The statement as written in the source, cut before its value. The
    #: elaborated signature is authoritative; this is what the author typed,
    #: shown beside it so neither form can hide what the other shows.
    statement: str | None = None
    probes: tuple[HypothesisProbe, ...] = ()
    checks: tuple[DefinitionCheck, ...] = ()
    witnesses: tuple[Witness, ...] = ()

    @property
    def findings(self) -> tuple[tuple[str, str], ...]:
        """``(code, reason)`` for every probe or check that succeeded."""

        found: list[tuple[str, str]] = []
        for probe in self.probes:
            if probe.proved:
                what = (
                    "every hypothesis deleted"
                    if probe.hypothesis == "*"
                    else f"hypothesis {probe.hypothesis} : {probe.hypothesis_type} deleted"
                )
                found.append(("hypothesis-unnecessary", f"{self.name} still proves by {probe.tactic} with {what}"))
        for check in self.checks:
            if not check.holds:
                continue
            if check.kind in {"always", "never"}:
                found.append(("definition-trivial", f"{self.name} {check.detail} (by {check.tactic})"))
            elif check.kind == "unused-argument":
                found.append(("definition-unused-argument", f"{self.name} never uses its argument {check.detail}"))
            elif check.kind == "redundant-clause":
                found.append(
                    ("definition-redundant-clause", f"in {self.name} the clause {check.detail} follows from the others (by {check.tactic})")
                )
        for witness in self.witnesses:
            if witness.status in {"mismatched", "sorry"}:
                found.append(("witness-invalid", f"{witness.name} is filed as a {witness.role} but is {witness.status}"))
        return tuple(found)

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
        """A fingerprint of what the skeleton means, stable under comments.

        An approval or a read-back is testimony about one skeleton. Recording
        this hash with it lets the audit tell when the skeleton has moved from
        under the testimony. Comments and docstrings are stripped first, so a
        clarified docstring does not revoke an approval, while any change to a
        signature or to a trusted definition's body does.
        """

        material = {
            "signature": _fold(self.signature),
            "source": _fold(strip_lean_comments(self.source or "")),
            "trusted": [
                [item.name, item.kind, _fold(item.signature), _fold(strip_lean_comments(item.source or ""))]
                for item in self.trusted
            ],
        }
        digest = hashlib.sha256(json.dumps(material, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
        return digest[:16]

    def blind_text(self) -> str:
        """The skeleton with every comment removed, for an auditor who must not see intent.

        A read-back is only evidence if its author did not know what the code
        was meant to say. Docstrings say exactly that, so they are stripped
        along with every other comment. Names stay: they are part of the code.
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
            "axioms": list(self.axioms),
            "checks": [item.as_dict() for item in self.checks],
            "declaration_lines": self.declaration_lines,
            "end_line": self.end_line,
            "hash": self.hash,
            "kind": self.kind,
            "module": self.module,
            "name": self.name,
            "path": self.path,
            "probes": [item.as_dict() for item in self.probes],
            "signature": self.signature,
            "skeleton_lines": self.skeleton_lines,
            "source": self.source,
            "start_line": self.start_line,
            "statement": self.statement,
            "trusted": [item.as_dict() for item in self.trusted],
            "witnesses": [item.as_dict() for item in self.witnesses],
        }


_WHITESPACE = re.compile(r"\s+")


def _fold(text: str) -> str:
    """Collapse whitespace so layout never changes a hash."""

    return _WHITESPACE.sub(" ", text).strip()


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
        is honestly incomplete; judged together they are the statement. The
        read-back auditor still gets one declaration at a time, since a
        read-back is testimony about one declaration.
        """

        parts = [f"-- article with {len(self.declarations)} declaration(s)"]
        parts += [declaration.blind_text() for declaration in self.declarations]
        return "\n".join(parts)

    @property
    def hash(self) -> str:
        """What an article's ``skeleton_approved`` records: one hash over all its skeletons."""

        if len(self.declarations) == 1:
            return self.declarations[0].hash
        joined = "\n".join(sorted(item.hash for item in self.declarations))
        return hashlib.sha256(joined.encode()).hexdigest()[:16]

    def as_dict(self) -> dict[str, object]:
        return {
            "article_path": self.article_path,
            "declarations": [item.as_dict() for item in self.declarations],
            "hash": self.hash,
            "node_id": self.node_id,
            "passage": self.passage,
            "passage_locator": self.passage_locator,
        }


@dataclass(frozen=True, slots=True)
class SkeletonReport:
    """Every skeleton the blueprint names, in article order."""

    nodes: tuple[NodeSkeleton, ...]
    unresolved: tuple[str, ...]
    schema: str = SKELETON_SCHEMA

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
    if not isinstance(data, dict) or data.get("schema") != SKELETON_SCHEMA:
        raise SkeletonError([f"{path} is not an {SKELETON_SCHEMA} report"])
    nodes = tuple(
        NodeSkeleton(
            node_id=str(node["node_id"]),
            article_path=str(node["article_path"]),
            declarations=tuple(_declaration_from_dict(item) for item in node["declarations"]),
            passage=_optional_str(node.get("passage")),
            passage_locator=_optional_str(node.get("passage_locator")),
        )
        for node in data.get("nodes", [])
    )
    return SkeletonReport(nodes=nodes, unresolved=tuple(str(item) for item in data.get("unresolved", [])))


def _declaration_from_dict(item: dict[str, object]) -> DeclarationSkeleton:
    return DeclarationSkeleton(
        name=str(item["name"]),
        kind=str(item["kind"]),
        module=str(item["module"]),
        path=_optional_str(item.get("path")),
        start_line=_optional_int(item.get("start_line")),
        end_line=_optional_int(item.get("end_line")),
        signature=str(item.get("signature", "")),
        trusted=tuple(
            TrustedDeclaration(
                name=str(trusted["name"]),
                kind=str(trusted["kind"]),
                module=str(trusted["module"]),
                path=_optional_str(trusted.get("path")),
                start_line=_optional_int(trusted.get("start_line")),
                end_line=_optional_int(trusted.get("end_line")),
                signature=str(trusted.get("signature", "")),
                depends=tuple(str(name) for name in trusted.get("depends", [])),
                source=_optional_str(trusted.get("source")),
            )
            for trusted in item.get("trusted", [])
        ),
        assumed=tuple(str(name) for name in item.get("assumed", [])),
        axioms=tuple(str(name) for name in item.get("axioms", [])),
        source=_optional_str(item.get("source")),
        statement=_optional_str(item.get("statement")),
        probes=_probes(item.get("probes")),
        checks=_checks(item.get("checks")),
        witnesses=_witnesses(item.get("witnesses")),
    )


def _probes(value: object) -> tuple[HypothesisProbe, ...]:
    if not isinstance(value, list):
        return ()
    return tuple(
        HypothesisProbe(
            hypothesis=str(item.get("hypothesis") or "?"),
            hypothesis_type=str(item.get("hypothesis_type") or item.get("type") or ""),
            statement=str(item.get("statement") or ""),
            proved=bool(item.get("proved")),
            tactic=_optional_str(item.get("tactic")),
        )
        for item in value
        if isinstance(item, dict)
    )


def _checks(value: object) -> tuple[DefinitionCheck, ...]:
    if not isinstance(value, list):
        return ()
    return tuple(
        DefinitionCheck(
            kind=str(item.get("kind") or "?"),
            detail=str(item.get("detail") or ""),
            holds=bool(item.get("holds")),
            tactic=_optional_str(item.get("tactic")),
        )
        for item in value
        if isinstance(item, dict)
    )


def _witnesses(value: object) -> tuple[Witness, ...]:
    if not isinstance(value, list):
        return ()
    return tuple(
        Witness(role=str(item.get("role") or "?"), name=str(item.get("name") or ""), status=str(item.get("status") or "?"))
        for item in value
        if isinstance(item, dict)
    )


def _optional_str(value: object) -> str | None:
    return None if value is None else str(value)


def _optional_int(value: object) -> int | None:
    return None if value is None else int(value)


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
    if toml.is_file():
        text = toml.read_bytes()
    elif (root / "lakefile.lean").is_file():
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
        try:
            result = subprocess.run(
                [lake, "translate-config", "toml", str(target)],
                cwd=str(root),
                capture_output=True,
                text=True,
                timeout=120,
                check=False,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise SkeletonError([f"lake translate-config failed: {exc}"]) from exc
        if result.returncode != 0 or not target.is_file():
            detail = (result.stderr or result.stdout).strip()[:300]
            raise SkeletonError([f"lake translate-config failed: {detail}"])
        return target.read_bytes()


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


#: The cheap automation a necessity probe may use. Order is cheapest first;
#: `exact?` is last because it searches the whole environment.
CORE_TACTICS: tuple[str, ...] = ("rfl", "trivial", "simp", "simp_all", "omega", "decide", "exact?")
MATHLIB_TACTICS: tuple[str, ...] = ("norm_num", "positivity", "linarith", "nlinarith", "aesop")

#: Heartbeats per tactic attempt, in `maxHeartbeats` option units. A tenth of
#: Lean's default: a probe that needs more is not "cheap automation".
PROBE_BUDGET = 20000


def render_probe(
    *,
    imports: tuple[str, ...],
    roots: tuple[str, ...],
    project_roots: tuple[str, ...],
    probe: bool = False,
    tactics: tuple[str, ...] = CORE_TACTICS,
) -> str:
    """Render the Lean program that extracts the skeleton of every root.

    With ``probe`` the program also runs the necessity probes, definition
    checks, and witness lookups, using ``tactics`` as its automation sweep.
    """

    if not roots:
        raise SkeletonError(["refusing to render a probe with no declarations"])
    if not imports:
        raise SkeletonError(["refusing to render a probe with no imports"])
    return _probe_template().format(
        budget=PROBE_BUDGET,
        core_roots=", ".join(_lean_name(name) for name in _CORE_MODULE_ROOTS),
        imports="\n".join(f"import {module}" for module in sorted(set(imports))),
        marker=PROBE_MARKER,
        probe_enabled="true" if probe else "false",
        project_roots=", ".join(_lean_name(name) for name in sorted(set(project_roots))),
        roots=", ".join(_lean_name(name) for name in roots),
        tactics=", ".join(f'({json.dumps(name)}, ← `(tactic| (intros; {name})))' for name in tactics),
    )


def project_tactics(lean_root: str | Path) -> tuple[str, ...]:
    """Core automation, plus Mathlib's when the project depends on it."""

    root = Path(lean_root).expanduser().resolve()
    manifest = root / "lake-manifest.json"
    has_mathlib = (root / ".lake" / "packages" / "mathlib").is_dir()
    if not has_mathlib and manifest.is_file():
        try:
            has_mathlib = '"mathlib"' in manifest.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            has_mathlib = False
    return CORE_TACTICS + MATHLIB_TACTICS if has_mathlib else CORE_TACTICS


def _lean_name(name: str) -> str:
    """Spell a Lean name as a term without trusting Lean to parse it."""

    result = "Name.anonymous"
    for part in name.split("."):
        result = f"Name.str ({result}) {json.dumps(part)}"
    return result


def run_probe(probe: str, lean_root: Path, *, timeout: float = DEFAULT_PROBE_TIMEOUT) -> str:
    """Run ``probe`` with ``lake env lean`` inside the built project."""

    lake = shutil.which("lake")
    if lake is None:
        raise SkeletonError(["lake is not on PATH; a built Lean project is required to extract skeletons"])
    with tempfile.TemporaryDirectory(prefix="autoform-skeleton-") as scratch:
        source = Path(scratch) / "AutoformSkeletonProbe.lean"
        source.write_text(probe, encoding="utf-8")
        env = os.environ.copy()
        env.pop("PYTHONPATH", None)
        try:
            result = subprocess.run(
                [lake, "env", "lean", str(source)],
                cwd=str(lean_root),
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
                env=env,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise SkeletonError([f"lake env lean failed: {exc}"]) from exc
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise SkeletonError([f"the skeleton probe failed; is the project built with `lake build`?\n{detail}"])
    return result.stdout


def parse_probe_output(text: str) -> dict[str, dict[str, object]]:
    """Return the JSON record the probe emitted for each root, keyed by name."""

    records: dict[str, dict[str, object]] = {}
    for line in text.splitlines():
        if not line.startswith(PROBE_MARKER):
            continue
        try:
            record = json.loads(line[len(PROBE_MARKER) :])
        except json.JSONDecodeError as exc:
            raise SkeletonError([f"the skeleton probe emitted invalid JSON: {exc}"]) from exc
        if not isinstance(record, dict) or not isinstance(record.get("root"), str):
            raise SkeletonError(["the skeleton probe emitted a record without a root name"])
        records[record["root"]] = record
    return records


# --------------------------------------------------------------------------- #
# Extraction
# --------------------------------------------------------------------------- #


def extract_skeletons(
    blueprint_dir: str | Path,
    *,
    lean_root: str | Path,
    runner: ProbeRunner | None = None,
    node_ids: tuple[str, ...] | None = None,
    probe: bool = False,
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
    libraries = lean_libraries(root)
    index = index_project(root)
    return extract_graph_skeletons(
        graph,
        lean_root=root,
        libraries=libraries,
        index=index,
        runner=runner or run_probe,
        node_ids=node_ids,
        probe=probe,
        tactics=project_tactics(root) if probe else CORE_TACTICS,
    )


def extract_graph_skeletons(
    graph: Graph,
    *,
    lean_root: Path,
    libraries: tuple[LeanLibrary, ...],
    index: SourceIndex,
    runner: ProbeRunner,
    node_ids: tuple[str, ...] | None = None,
    probe: bool = False,
    tactics: tuple[str, ...] = CORE_TACTICS,
) -> SkeletonReport:
    """Extract skeletons for an already loaded graph."""

    selected = [graph.nodes[node_id] for node_id in sorted(graph.nodes) if graph.nodes[node_id].lean]
    if node_ids is not None:
        wanted = set(node_ids)
        unknown = sorted(wanted - set(graph.nodes))
        if unknown:
            raise SkeletonError([f"unknown article: {node_id}" for node_id in unknown])
        selected = [node for node in selected if node.id in wanted]

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
    if roots:
        # Witnesses may live in any module of the library, so its root module
        # is imported alongside the modules that hold the declarations.
        library_roots = {
            root
            for library in libraries
            for root in library.roots
            if path_of(root, libraries, lean_root) is not None
        }
        program = render_probe(
            imports=tuple(sorted(imports | library_roots)),
            roots=tuple(roots),
            project_roots=tuple(root for library in libraries for root in library.roots),
            probe=probe,
            tactics=tactics,
        )
        records = parse_probe_output(runner(program, lean_root))

    nodes: list[NodeSkeleton] = []
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
            declarations.append(_declaration(record, libraries=libraries, lean_root=lean_root, index=index))
        passage, locator = source_passage(node, graph.blueprint_dir)
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
            # Lines are what an editor or `sed` counts: newline-separated. Python's
            # `splitlines` also breaks on form feeds, which `pdftotext` writes
            # between pages, and every locator into such a file would then drift
            # by one line per page.
            lines = candidate.read_text(encoding="utf-8").split("\n")
        except (ValueError, OSError, UnicodeError):
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
        trusted=tuple(_dependency_order(trusted)),
        assumed=tuple(_strings(record.get("assumed"))),
        axioms=tuple(_strings(record.get("axioms"))),
        statement=_statement(record.get("statement_source")),
        probes=_probes(record.get("probes")),
        checks=_checks(record.get("checks")),
        witnesses=_witnesses(record.get("witnesses")),
    )
    if not declaration.defines:
        return declaration
    return replace(declaration, source=source_excerpt(declaration, lean_root))


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
        depends=tuple(_strings(item.get("depends"))),
    )
    # The report is the artifact later stages read, so the quoted source
    # travels with it rather than depending on the Lean tree being present.
    return replace(trusted, source=source_excerpt(trusted, lean_root))


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
    try:
        lines = (lean_root / item.path).read_text(encoding="utf-8").split("\n")
    except (OSError, UnicodeError):
        return None
    if item.start_line < 1 or item.end_line > len(lines) or item.end_line < item.start_line:
        return None
    return "\n".join(lines[item.start_line - 1 : item.end_line])


def format_report(report: SkeletonReport, *, lean_root: Path | None = None) -> str:
    """Render the report as the text a reviewer reads.

    With ``lean_root`` the trusted declarations are quoted from the sources;
    without it only their names and locations are listed.
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
            out.extend(f"   {line}" for line in _probe_lines(declaration))
            for item in declaration.trusted:
                out.append("")
                out.append(f"   -- {item.kind} {item.name}  ({_where(item)})")
                out.extend(f"   -- {line}" for line in item.signature.splitlines())
                excerpt = item.source
                if excerpt is None and lean_root is not None:
                    excerpt = source_excerpt(item, lean_root)
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


def write_packets(
    report: SkeletonReport,
    directory: str | Path,
    *,
    passages: str | Path | None = None,
) -> list[Path]:
    """Write one blind packet per skeleton for independent read-back auditors.

    Each packet holds only what the auditor may see: the comment-stripped
    skeleton. Nothing names the article, the source, or the intent. The
    manifest beside the packets maps each file back to its article and hash so
    the read-backs can be filed and checked, without the auditor reading it.

    With ``passages``, the source passage each article cites is written to a
    second directory, one ``passage.txt`` per article. A faithfulness judge
    gets a packet and its passage; a read-back auditor gets the packet alone,
    which is why the two never share a directory.
    """

    root = Path(directory).expanduser()
    root.mkdir(parents=True, exist_ok=True)
    passages_root = Path(passages).expanduser() if passages is not None else None
    written: list[Path] = []
    manifest: list[dict[str, str]] = []
    for node in report.nodes:
        passage_path: str | None = None
        if passages_root is not None and node.passage is not None:
            target = passages_root / Path(*node.node_id.split("/")) / "passage.txt"
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(node.passage + "\n", encoding="utf-8")
            passage_path = target.relative_to(passages_root).as_posix()
        if node.declarations:
            article = root / Path(*node.node_id.split("/")) / ARTICLE_PACKET
            article.parent.mkdir(parents=True, exist_ok=True)
            article.write_text(node.blind_text(), encoding="utf-8")
            written.append(article)
        for declaration in node.declarations:
            relative = Path(*node.node_id.split("/")) / f"{declaration.name}.lean"
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(declaration.blind_text(), encoding="utf-8")
            written.append(path)
            entry = {
                "article_packet": (Path(*node.node_id.split("/")) / ARTICLE_PACKET).as_posix(),
                "declaration": declaration.name,
                "hash": declaration.hash,
                "node_id": node.node_id,
                "packet": relative.as_posix(),
            }
            if passage_path is not None:
                entry["passage"] = passage_path
                entry["passage_locator"] = node.passage_locator or ""
            manifest.append(entry)
    (root / PACKET_MANIFEST).write_text(
        json.dumps({"packets": manifest, "schema": SKELETON_SCHEMA}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return written


def _probe_lines(declaration: DeclarationSkeleton) -> list[str]:
    """Summarize probes, checks, and witnesses for the text report."""

    lines: list[str] = []
    if declaration.probes:
        flagged = [probe for probe in declaration.probes if probe.proved]
        if flagged:
            for probe in flagged:
                what = "every hypothesis" if probe.hypothesis == "*" else f"{probe.hypothesis} : {probe.hypothesis_type}"
                lines.append(f"probe: PROVES WITHOUT {what} (by {probe.tactic})")
        else:
            lines.append(f"probe: no hypothesis found unnecessary ({len(declaration.probes)} attempts)")
    if declaration.checks:
        flagged = [check for check in declaration.checks if check.holds]
        if flagged:
            for check in flagged:
                lines.append(f"check: {check.kind.upper()} {check.detail}" + (f" (by {check.tactic})" if check.tactic else ""))
        else:
            lines.append(f"check: not trivial, no unused argument, no redundant clause ({len(declaration.checks)} checks)")
    if declaration.witnesses:
        lines.append("witnesses: " + " · ".join(f"{item.role} {item.status}" for item in declaration.witnesses))
    return lines


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
    "SKELETON_SCHEMA",
    "CORE_TACTICS",
    "DeclarationSkeleton",
    "DefinitionCheck",
    "HypothesisProbe",
    "LeanLibrary",
    "MATHLIB_TACTICS",
    "PROBE_BUDGET",
    "NodeSkeleton",
    "PACKET_MANIFEST",
    "ProbeRunner",
    "SkeletonError",
    "SkeletonReport",
    "TrustedDeclaration",
    "Witness",
    "extract_graph_skeletons",
    "extract_skeletons",
    "format_report",
    "lean_libraries",
    "load_skeleton_report",
    "module_of",
    "parse_probe_output",
    "path_of",
    "project_tactics",
    "render_probe",
    "run_probe",
    "source_excerpt",
    "source_passage",
    "write_packets",
]
