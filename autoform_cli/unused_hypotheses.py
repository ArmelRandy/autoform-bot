"""Hypotheses that the proof of a blueprint theorem never uses.

A theorem can compile and be true while one of its hypotheses plays no part.
Either the source states a hypothesis it does not need, or the formal statement
says less than the source, so that the hypothesis has nothing left to do.
Either way a reviewer should know.

The proof answers this exactly. It is a term the kernel has checked; a
hypothesis the term never mentions can be deleted, and the same term proves
what remains. ``autoform unused-hypotheses`` reads the proof of every theorem
an article names in the built environment, the same way ``autoform skeleton``
reads its statements, and adds nothing to the skeleton report, its packets, or
its hashes. A hypothesis the proof does use may still be unnecessary; only the
other direction is certain.

Lean's own linters already warn about a named hypothesis the proof never
references. This also reports the ones they skip: a name starting with ``_``,
an unnamed instance argument, the antecedent of ``p → q``, and a binder such as
``∀ n > 0``.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from .graph import GraphValidationError, load_graph
from .lean import index_failure_message, index_project
from .skeleton import (
    DEFAULT_PROBE_TIMEOUT,
    PROBE_OUTPUT_ENV,
    ProbeRunner,
    SkeletonError,
    UnresolvedTarget,
    _lean_name,
    lean_libraries,
    locate_declaration,
    resolve_lean_root,
    run_probe,
    select_lean_targets,
)

REPORT_SCHEMA = "autoform-unused-hypotheses/v1"

#: Every line the probe wants read back starts with this marker, so Lean's own
#: informational output can never be mistaken for a result.
PROBE_MARKER = "AUTOFORM_UNUSED_HYPOTHESES "

#: What the probe says about a declaration's proof: read, containing ``sorry``
#: itself (a term that uses nothing, so it is not read), or not a theorem.
_PROOFS = frozenset({"proved", "sorry", "none"})
_KINDS = frozenset({"theorem", "axiom", "def", "opaque", "inductive", "other"})


@dataclass(frozen=True, slots=True)
class Hypothesis:
    """A propositional hypothesis that could be deleted from a theorem.

    ``position`` counts the theorem's binders from 1. ``name`` is ``_`` for a
    binder no reader named. ``used`` is false only when the proof term never
    mentions the hypothesis, which makes the weakened statement a theorem with
    the same proof.
    """

    position: int
    name: str
    type: str
    used: bool

    @property
    def label(self) -> str:
        return f"argument {self.position}" if self.name == "_" else self.name

    def as_dict(self) -> dict[str, object]:
        return {"name": self.name, "position": self.position, "type": self.type, "used": self.used}


@dataclass(frozen=True, slots=True)
class DeclarationHypotheses:
    """What the probe read about one declaration an article names."""

    node_id: str
    name: str
    kind: str
    #: ``proved``, ``sorry`` or ``none`` (not a theorem).
    proof: str
    #: The hypotheses that could be deleted; empty unless ``proof`` is ``proved``.
    #: One that the conclusion or a later binder mentions is not listed.
    hypotheses: tuple[Hypothesis, ...]

    @property
    def findings(self) -> tuple[str, ...]:
        return tuple(
            f"the proof never uses {item.label} : {item.type}" for item in self.hypotheses if not item.used
        )

    def as_dict(self) -> dict[str, object]:
        return {
            "hypotheses": [item.as_dict() for item in self.hypotheses],
            "kind": self.kind,
            "name": self.name,
            "node_id": self.node_id,
            "proof": self.proof,
        }


@dataclass(frozen=True, slots=True)
class UnusedHypothesesReport:
    """Every declaration read, in article order, and every one left unread."""

    declarations: tuple[DeclarationHypotheses, ...]
    unresolved: tuple[UnresolvedTarget, ...]
    schema: str = REPORT_SCHEMA

    @property
    def findings(self) -> tuple[str, ...]:
        """Every finding, as ``node: declaration: hypothesis-unused: reason``."""

        return tuple(
            f"{item.node_id}: {item.name}: hypothesis-unused: {finding}"
            for item in self.declarations
            for finding in item.findings
        )

    @property
    def clean(self) -> bool:
        """Every name was read. Findings are for a reviewer and never fail the
        run: the source may state a hypothesis its theorem does not need."""

        return not self.unresolved

    def as_dict(self) -> dict[str, object]:
        return {
            "declarations": [item.as_dict() for item in self.declarations],
            "findings": list(self.findings),
            "schema": self.schema,
            "unresolved": [item.as_dict() for item in self.unresolved],
        }

    def to_json(self) -> str:
        return json.dumps(self.as_dict(), sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def find_unused_hypotheses(
    blueprint_dir: str | Path,
    *,
    lean_root: str | Path,
    node_ids: tuple[str, ...] | None = None,
    runner: ProbeRunner | None = None,
    timeout: float = DEFAULT_PROBE_TIMEOUT,
) -> UnusedHypothesesReport:
    """Read the proof of every ``lean:`` declaration the selected articles name.

    Articles are selected and declarations placed as ``autoform skeleton`` does
    it. ``runner`` executes the rendered probe and returns its records; tests
    pass a fake.
    """

    try:
        graph = load_graph(blueprint_dir)
    except GraphValidationError as exc:
        raise SkeletonError(exc.issues) from exc
    root = resolve_lean_root(lean_root)
    _, selected, _ = select_lean_targets(graph, node_ids)
    libraries = lean_libraries(root)
    try:
        index = index_project(root)
    except OSError as error:
        raise SkeletonError([index_failure_message(error)]) from error

    unresolved: list[UnresolvedTarget] = []
    requests: list[tuple[str, str]] = []
    imports: set[str] = set()
    for node, names in selected:
        for name in names:
            module, reason = locate_declaration(name, index=index, libraries=libraries, lean_root=root)
            if module is None:
                unresolved.append(UnresolvedTarget(node.id, name, reason or ""))
                continue
            imports.add(module)
            requests.append((node.id, name))
    if not requests:
        return UnusedHypothesesReport(declarations=(), unresolved=tuple(unresolved))

    roots = tuple(dict.fromkeys(name for _, name in requests))
    execute = runner or (
        lambda probe, lean_root_: run_probe(probe, lean_root_, timeout=timeout, label="unused-hypotheses probe")
    )
    try:
        output = execute(render_probe(imports=tuple(sorted(imports)), roots=roots), root)
        current = index_project(root)
    except OSError as error:
        raise SkeletonError([index_failure_message(error)]) from error
    # An answer is about the sources it was computed from. If they changed
    # while Lean ran, it may describe a state that no longer exists.
    if current.source_digest != index.source_digest:
        raise SkeletonError(["Lean sources changed while the probe ran; retry after the build is idle"])
    records = parse_probe_output(output, expected_roots=roots)

    declarations: list[DeclarationHypotheses] = []
    for node_id, name in requests:
        record = records[name]
        if not record["found"]:
            unresolved.append(UnresolvedTarget(node_id, name, "declaration not found in the built environment"))
            continue
        declarations.append(
            DeclarationHypotheses(
                node_id=node_id,
                name=name,
                kind=str(record["kind"]),
                proof=str(record["proof"]),
                hypotheses=_hypotheses(record["hypotheses"], root=name),
            )
        )
    return UnusedHypothesesReport(declarations=tuple(declarations), unresolved=tuple(unresolved))


def _probe_template() -> str:
    """The Lean probe source, kept under probes/ beside this module."""

    return (Path(__file__).parent / "probes" / "unused_hypotheses.lean").read_text(encoding="utf-8")


def render_probe(*, imports: tuple[str, ...], roots: tuple[str, ...]) -> str:
    """Render the Lean program that reads the proof of every root."""

    if not roots:
        raise SkeletonError(["refusing to render a probe with no declarations"])
    if not imports:
        raise SkeletonError(["refusing to render a probe with no imports"])
    return _probe_template().format(
        imports="\n".join(f"import {module}" for module in sorted(set(imports))),
        marker=PROBE_MARKER,
        output_env=PROBE_OUTPUT_ENV,
        roots=", ".join(f"({json.dumps(name, ensure_ascii=False)}, {_lean_name(name)})" for name in roots),
    )


def parse_probe_output(output: str, *, expected_roots: tuple[str, ...]) -> dict[str, dict[str, object]]:
    """Strictly read one record per requested root out of the probe's output."""

    expected = set(expected_roots)
    records: dict[str, dict[str, object]] = {}
    for line in output.splitlines():
        if not line.startswith(PROBE_MARKER):
            continue
        try:
            record = json.loads(line[len(PROBE_MARKER) :])
        except json.JSONDecodeError as exc:
            raise SkeletonError([f"the unused-hypotheses probe wrote a line that is not JSON: {exc}"]) from exc
        if not isinstance(record, dict) or not isinstance(record.get("root"), str):
            raise SkeletonError(["the unused-hypotheses probe wrote a record without a root name"])
        root = record["root"]
        if root not in expected:
            raise SkeletonError([f"the unused-hypotheses probe answered for an unrequested declaration: {root}"])
        if root in records:
            raise SkeletonError([f"the unused-hypotheses probe answered twice for {root}"])
        found = record.get("found")
        if type(found) is not bool:
            raise SkeletonError([f"the unused-hypotheses probe wrote a non-boolean found field for {root}"])
        if record.keys() != ({"found", "hypotheses", "kind", "proof", "root"} if found else {"found", "root"}):
            raise SkeletonError([f"the unused-hypotheses probe wrote invalid fields for {root}"])
        if found:
            kind, proof = record["kind"], record["proof"]
            if kind not in _KINDS or proof not in _PROOFS:
                raise SkeletonError([f"the unused-hypotheses probe wrote an unknown kind or proof state for {root}"])
            if (proof == "none") != (kind != "theorem"):
                raise SkeletonError(
                    [f"the unused-hypotheses probe read a proof of {root} exactly when it is not a theorem"]
                )
            if _hypotheses(record["hypotheses"], root=root) and proof != "proved":
                raise SkeletonError(
                    [f"the unused-hypotheses probe listed hypotheses of {root} without reading its proof"]
                )
        records[root] = record
    missing = [root for root in expected_roots if root not in records]
    if missing:
        raise SkeletonError([f"the unused-hypotheses probe gave no answer for {missing[0]}"])
    return records


def _hypotheses(value: object, *, root: str) -> tuple[Hypothesis, ...]:
    """Strictly read the hypotheses listed for one theorem."""

    if not isinstance(value, list):
        raise SkeletonError([f"malformed hypotheses for {root}"])
    hypotheses: list[Hypothesis] = []
    for item in value:
        if not isinstance(item, dict) or item.keys() != {"name", "position", "type", "used"}:
            raise SkeletonError([f"malformed hypothesis entry for {root}"])
        position, name, type_, used = item["position"], item["name"], item["type"], item["used"]
        if (
            type(position) is not int
            or position < 1
            or not isinstance(name, str)
            or not name
            or not isinstance(type_, str)
            or not type_
            or type(used) is not bool
        ):
            raise SkeletonError([f"malformed hypothesis entry for {root}"])
        # Lean's printer wraps a long type over several lines; a finding is one.
        hypotheses.append(Hypothesis(position=position, name=name, type=" ".join(type_.split()), used=used))
    return tuple(hypotheses)


def format_unused_hypotheses(report: UnusedHypothesesReport) -> str:
    """The report for a person: one line per declaration, then findings and gaps."""

    lines: list[str] = []
    current = None
    for item in report.declarations:
        if item.node_id != current:
            lines.append(item.node_id)
            current = item.node_id
        if item.proof == "sorry":
            summary = ": the proof contains sorry, so it was not read"
        elif item.hypotheses:
            unused = sum(not hypothesis.used for hypothesis in item.hypotheses)
            summary = f": {unused} of {len(item.hypotheses)} hypotheses unused"
        else:
            summary = ""
        lines.append(f"  {item.name} ({item.kind}){summary}")
    lines += [f"finding: {finding}" for finding in report.findings]
    lines += [f"error: {item.message}" for item in report.unresolved]
    return "\n".join(lines) + "\n" if lines else "no Lean declarations to read\n"


__all__ = [
    "PROBE_MARKER",
    "REPORT_SCHEMA",
    "DeclarationHypotheses",
    "Hypothesis",
    "UnusedHypothesesReport",
    "find_unused_hypotheses",
    "format_unused_hypotheses",
    "parse_probe_output",
    "render_probe",
]
