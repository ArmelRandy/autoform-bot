from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_cli import unused_hypotheses
from autoform_cli.__main__ import main
from autoform_cli.skeleton import SkeletonError
from autoform_cli.unused_hypotheses import (
    PROBE_MARKER,
    find_unused_hypotheses,
    format_unused_hypotheses,
    parse_probe_output,
    render_probe,
)
from tests.test_skeleton import _blueprint, _build, _lean_toolchain_available, _project


def _record(root: str, **fields: object) -> str:
    return PROBE_MARKER + json.dumps({"root": root, **fields})


def _theorem(root: str, *hypotheses: tuple[int, str, str, bool], proof: str = "proved") -> str:
    listed = [
        {"position": position, "name": name, "type": type_, "used": used}
        for position, name, type_, used in hypotheses
    ]
    return _record(root, found=True, kind="theorem", proof=proof, hypotheses=listed)


def _definition(root: str) -> str:
    return _record(root, found=True, kind="def", proof="none", hypotheses=[])


def test_the_probe_lifts_lean_s_command_heartbeat_limit() -> None:
    # All declarations run in one command; under Lean's default limit a real
    # project ran out of heartbeats. The CLI's timeout bounds the run instead.
    probe = render_probe(imports=("Skel",), roots=("Skel.heavy",))

    assert "set_option maxHeartbeats 0 in\nrun_cmd do" in probe


@pytest.mark.parametrize(
    ("lines", "message"),
    [
        ([_record("B.q", found=False)], "unrequested declaration"),
        ([_record("A.p", found=False), _record("A.p", found=False)], "twice"),
        ([], "no answer for A.p"),
        ([_record("A.p", found="yes")], "non-boolean found"),
        ([_record("A.p", found=True, kind="lemma", proof="proved", hypotheses=[])], "unknown kind or proof"),
        ([_theorem("A.p", (1, "h", "P", False), proof="sorry")], "without reading its proof"),
        ([_record("A.p", found=True, kind="def", proof="proved", hypotheses=[])], "exactly when it is not a theorem"),
        ([_record("A.p", found=True, kind="theorem", proof="proved")], "invalid fields"),
        ([_theorem("A.p", (0, "h", "P", False))], "malformed hypothesis entry"),
    ],
    ids=[
        "answer-for-another-name",
        "two-answers",
        "no-answer",
        "non-boolean-found",
        "unknown-kind",
        "hypotheses-of-an-unread-proof",
        "proof-of-a-def",
        "missing-field",
        "position-zero",
    ],
)
def test_parse_refuses_answers_that_do_not_fit_the_question(lines: list[str], message: str) -> None:
    with pytest.raises(SkeletonError, match=message):
        parse_probe_output("\n".join(lines), expected_roots=("A.p",))


def test_an_unused_hypothesis_is_a_finding_that_does_not_fail(tmp_path: Path) -> None:
    project = _project(tmp_path)
    lean = {"eligible": "Skel.Eligible", "heavy": "Skel.heavy_of_weight", "pending": "Skel.observation_determined"}
    blueprint = _blueprint(tmp_path, lean=lean)
    output = "\n".join(
        [
            _definition("Skel.Eligible"),
            # Lean's printer wraps a long type; the finding keeps it on one line.
            _theorem("Skel.heavy_of_weight", (3, "h", "0 <\n    y", False), (4, "_", "Fact p", False)),
            _theorem("Skel.observation_determined", proof="sorry"),
        ]
    )

    report = find_unused_hypotheses(blueprint, lean_root=project, runner=lambda probe, root: output)

    # The source may state a hypothesis its theorem does not need: a reviewer
    # decides, so the run passes.
    assert report.clean
    assert report.findings == (
        "basics/heavy: Skel.heavy_of_weight: hypothesis-unused: the proof never uses h : 0 < y",
        "basics/heavy: Skel.heavy_of_weight: hypothesis-unused: the proof never uses argument 4 : Fact p",
    )
    text = format_unused_hypotheses(report)
    assert "  Skel.heavy_of_weight (theorem): 2 of 2 hypotheses unused\n" in text
    assert "  Skel.observation_determined (theorem): the proof contains sorry, so it was not read\n" in text
    assert "  Skel.Eligible (def)\n" in text
    assert "\nerror:" not in text


def test_unresolved_declarations_are_reported_and_fail(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"absent": "Skel.absent", "heavy": "Skel.heavy_of_weight, Skel.Eligible"})
    output = "\n".join([_record("Skel.heavy_of_weight", found=False), _definition("Skel.Eligible")])

    report = find_unused_hypotheses(blueprint, lean_root=project, runner=lambda probe, root: output)

    assert [item.message for item in report.unresolved] == [
        "basics/absent: Skel.absent: declaration not found in the Lean sources",
        "basics/heavy: Skel.heavy_of_weight: declaration not found in the built environment",
    ]
    assert [item.name for item in report.declarations] == ["Skel.Eligible"]
    assert not report.clean


def test_nothing_placed_reports_without_running_lean(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"absent": "Skel.absent"})

    def runner(probe: str, root: Path) -> str:
        raise AssertionError("no declaration was placed, so Lean must not run")

    report = find_unused_hypotheses(blueprint, lean_root=project, runner=runner)

    assert [item.declaration for item in report.unresolved] == ["Skel.absent"]


def test_the_probe_imports_only_the_modules_it_reads_and_narrows_to_the_selection(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"heavy": "Skel.heavy_of_weight", "unambiguous": "Skel.NonAmbiguous"})
    asked: list[str] = []

    def runner(probe: str, root: Path) -> str:
        asked.append(probe)
        return _theorem("Skel.heavy_of_weight")

    report = find_unused_hypotheses(blueprint, lean_root=project, node_ids=("basics/heavy",), runner=runner)

    assert [item.node_id for item in report.declarations] == ["basics/heavy"]
    # Lake checks the freshness of everything imported, so nothing else is.
    assert [line for line in asked[0].splitlines() if line.startswith("import Skel")] == ["import Skel.Main"]
    assert "NonAmbiguous" not in asked[0]


def test_duplicate_targets_are_refused(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"heavy": "Skel.heavy_of_weight, Skel.heavy_of_weight"})

    with pytest.raises(SkeletonError, match="duplicate Lean declaration target"):
        find_unused_hypotheses(blueprint, lean_root=project, runner=lambda probe, root: "")


def test_sources_edited_while_lean_runs_are_refused(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"heavy": "Skel.heavy_of_weight"})

    def runner(probe: str, root: Path) -> str:
        with (root / "Skel" / "Main.lean").open("a", encoding="utf-8") as handle:
            handle.write("-- edited\n")
        return _theorem("Skel.heavy_of_weight")

    with pytest.raises(SkeletonError, match="Lean sources changed"):
        find_unused_hypotheses(blueprint, lean_root=project, runner=runner)


def test_cli_exit_codes_json_and_timeout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"heavy": "Skel.heavy_of_weight"})
    answers = iter(
        [
            _theorem("Skel.heavy_of_weight", (3, "h", "0 < y", False)),
            _theorem("Skel.heavy_of_weight", (3, "h", "0 < y", False)),
            _record("Skel.heavy_of_weight", found=False),
        ]
    )
    timeouts: list[float] = []

    def fake_run_probe(probe: str, root: Path, *, timeout: float, label: str) -> str:
        timeouts.append(timeout)
        return next(answers)

    monkeypatch.setattr(unused_hypotheses, "run_probe", fake_run_probe)
    command = ["unused-hypotheses", str(blueprint), "--lean-root", str(project)]

    assert main([*command, "--json", "--timeout", "30"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["schema"] == "autoform-unused-hypotheses/v1"
    assert payload["declarations"][0]["hypotheses"] == [{"name": "h", "position": 3, "type": "0 < y", "used": False}]
    assert main(command) == 0
    assert "finding: basics/heavy: Skel.heavy_of_weight: hypothesis-unused" in capsys.readouterr().out
    # A name Lean cannot find fails the run; a finding does not.
    assert main(command) == 1
    assert timeouts == [30.0, unused_hypotheses.DEFAULT_PROBE_TIMEOUT, unused_hypotheses.DEFAULT_PROBE_TIMEOUT]
    assert main([*command, "--node", "nope"]) == 2


def test_cli_reports_a_lean_root_that_cannot_be_resolved(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    blueprint = _blueprint(tmp_path, lean={"heavy": "Skel.heavy_of_weight"})

    assert main(["unused-hypotheses", str(blueprint), "--lean-root", "~nosuchuser-autoform/x"]) == 2
    assert "error: Lean root ~nosuchuser-autoform/x cannot be resolved" in capsys.readouterr().err


_UNUSED = """\
import Skel.Main

namespace Skel

variable {Y : Type}

class PosFact (n : Nat) : Prop where
  pos : 0 < n

-- The hypothesis is not used.
theorem needless (y : Y) (h : y = y) : y = y := rfl
-- `same` mentions `h`, so `h` cannot be deleted on its own; `same` can.
theorem chain (n : Nat) (h : 0 < n) (same : h = h) : n = n := rfl
-- The conclusion mentions `h`, so it cannot be deleted.
theorem stated (p : Prop) (h : p) : h = h := rfl
-- A proof that is another theorem may use anything: nothing is claimed unused.
theorem via : ∀ (y : Nat) (h : y = y), y = y := needless
-- Two instance hypotheses of one type, whose names no reader wrote.
theorem inst (n : Nat) [PosFact n] [PosFact n] : 0 < n + 1 := Nat.succ_pos n
-- An auto-param hypothesis.
theorem auto (n : Nat) (h : 0 < n + 1 := by omega) : True := trivial
-- The term of a `sorry` uses nothing, so it says nothing.
theorem pending (n : Nat) (h : 0 < n) : 0 < n := sorry
-- `m` is not a proposition, so it is not a hypothesis.
theorem extra (n m : Nat) (h : n = n) : n = n := rfl
-- A complete proof that uses an open statement is read.
theorem conditional (n : Nat) (h : 0 < n) (u : n = n) : 0 < n := pending n h
-- Lean's unused-variables linter skips these two; the command does not.
theorem underscored (n : Nat) (_h : n = n) : True := trivial
theorem boundedForall : ∀ n > 0, n = n := fun _ _ => rfl

section
variable {p : Nat} [PosFact p]
-- A section instance the proof never needs, and the `omit` that removes it.
theorem sectionInst (h : p = p) : p = p := h
omit [PosFact p] in
theorem sectionOmit (h : p = p) : p = p := h
end

end Skel
"""


@pytest.mark.skipif(not _lean_toolchain_available(), reason="needs lake and the fixture's Lean toolchain")
def test_unused_hypotheses_in_a_built_project(tmp_path: Path) -> None:
    project = _project(tmp_path)
    (project / "Skel" / "Unused.lean").write_text(_UNUSED, encoding="utf-8")
    with (project / "Skel.lean").open("a", encoding="utf-8") as handle:
        handle.write("import Skel.Unused\n")
    _build(project)
    names = (
        "Eligible auto boundedForall chain conditional extra heavy_of_weight inst needless pending"
        " sectionInst sectionOmit stated underscored via"
    ).split()
    blueprint = _blueprint(tmp_path, lean={name.lower(): f"Skel.{name}" for name in names})

    report = find_unused_hypotheses(blueprint, lean_root=project)

    assert report.unresolved == ()
    read = {
        item.name: (item.proof, [(h.position, h.name, h.type, h.used) for h in item.hypotheses])
        for item in report.declarations
    }
    assert read == {
        "Skel.needless": ("proved", [(3, "h", "y = y", False)]),
        "Skel.heavy_of_weight": ("proved", [(4, "h", "0 < Skel.HasWeight.weight y", True)]),
        "Skel.chain": ("proved", [(3, "same", "h = h", False)]),
        "Skel.stated": ("proved", []),
        "Skel.via": ("proved", [(2, "h", "y = y", True)]),
        "Skel.inst": ("proved", [(2, "_", "Skel.PosFact n", False), (3, "_", "Skel.PosFact n", False)]),
        "Skel.auto": ("proved", [(2, "h", "0 < n + 1", False)]),
        "Skel.pending": ("sorry", []),
        "Skel.extra": ("proved", [(3, "h", "n = n", False)]),
        "Skel.conditional": ("proved", [(2, "h", "0 < n", True), (3, "u", "n = n", False)]),
        "Skel.underscored": ("proved", [(2, "_h", "n = n", False)]),
        "Skel.boundedForall": ("proved", [(2, "_", "n > 0", False)]),
        "Skel.sectionInst": ("proved", [(2, "_", "Skel.PosFact p", False), (3, "h", "p = p", True)]),
        "Skel.sectionOmit": ("proved", [(2, "h", "p = p", True)]),
        "Skel.Eligible": ("none", []),
    }
    inst = next(item for item in report.declarations if item.name == "Skel.inst")
    assert inst.findings == (
        "the proof never uses argument 2 : Skel.PosFact n",
        "the proof never uses argument 3 : Skel.PosFact n",
    )
