from __future__ import annotations

import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import time
from dataclasses import replace
from pathlib import Path

import pytest
import psutil

from autoform_cli.__main__ import main
from autoform_cli.skeleton import (
    PACKET_MANIFEST,
    PROBE_MARKER,
    SKELETON_SCHEMA,
    SkeletonReport,
    SkeletonError,
    _install_output,
    _join_readers,
    _remove_output,
    _rename_no_replace,
    _run_bounded_command,
    _replace_outputs,
    _stage_output,
    _hash_module_files,
    extract_skeletons,
    format_report,
    lean_libraries,
    load_skeleton_report,
    module_of,
    parse_probe_output,
    path_of,
    render_probe,
    run_probe,
    write_packets,
    write_skeleton_report,
)

_FIXTURE = Path(__file__).resolve().parent / "fixtures" / "skeleton-project"


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #


def _blueprint(root: Path, *, lean: dict[str, str]) -> Path:
    """Write a vault whose articles name the given ``lean:`` declarations."""

    blueprint = root / "blueprint"
    chapter = blueprint / "roadmap" / "basics"
    chapter.mkdir(parents=True)
    (blueprint / "roadmap" / "README.md").write_text("# Roadmap\n", encoding="utf-8")
    (chapter / "README.md").write_text("# Basics\n", encoding="utf-8")
    for stem, names in lean.items():
        (chapter / f"{stem}.md").write_text(
            f"---\ndeclaration: theorem\nlean: {names}\n---\n\n# {stem}\n\nA statement.\n\n"
            "## Depends on\n\nNone.\n",
            encoding="utf-8",
        )
    coverage = blueprint / "coverage"
    coverage.mkdir()
    (coverage / "README.md").write_text(
        "# Coverage\n\n| Area | Coverage | Evidence |\n| --- | --- | --- |\n| All | OUT | scratch |\n",
        encoding="utf-8",
    )
    return blueprint


def _project(root: Path, *, src_dir: str = ".") -> Path:
    """Write an unbuilt copy of the fixture project, optionally under ``src_dir``."""

    project = root / "project"
    project.mkdir()
    shutil.copy(_FIXTURE / "lean-toolchain", project / "lean-toolchain")
    lakefile = (_FIXTURE / "lakefile.toml").read_text(encoding="utf-8")
    if src_dir != ".":
        lakefile += f'srcDir = "{src_dir}"\n'
    (project / "lakefile.toml").write_text(lakefile, encoding="utf-8")
    source_root = project / src_dir
    shutil.copytree(_FIXTURE / "Skel", source_root / "Skel")
    shutil.copy(_FIXTURE / "Skel.lean", source_root / "Skel.lean")
    return project


def _record(root: str, **fields: object) -> str:
    return PROBE_MARKER + json.dumps({"root": root, **fields})


def _semantic(payload: dict[str, object]) -> str:
    return json.dumps({"generated": [], "root": payload}, separators=(",", ":"))


def _fake_probe_output(*, include_ghost: bool = False) -> str:
    """What the probe says about the fixture, as captured from a real run."""

    eligible = {
        "name": "Skel.Eligible",
        "kind": "def",
        "module": "Skel.Defs",
        "range": [5, 6],
        "signature": "Skel.Eligible {Y : Type} (S : Y → Prop) (y : Y) : Prop",
        "semantic_schema": "autoform-lean-expr/v2",
        "semantic": _semantic({"type": {"sort": {"zero": None}}, "value": {"bvar": 0}}),
        "depends": [],
        "source": "/-- A weak observation admits a label. -/\ndef Eligible (S : Y → Prop) (y : Y) : Prop := S y",
    }
    non_ambiguous = {
        "name": "Skel.NonAmbiguous",
        "kind": "def",
        "module": "Skel.Defs",
        "range": [8, 10],
        "signature": "Skel.NonAmbiguous {Y : Type} (S : Y → Prop) : Prop",
        "semantic_schema": "autoform-lean-expr/v2",
        "semantic": _semantic({"type": {"sort": {"zero": None}}, "value": {"bvar": 1}}),
        "depends": ["Skel.Eligible"],
        "source": (
            "/-- At most one label is admitted. -/\n"
            "def NonAmbiguous (S : Y → Prop) : Prop :=\n"
            "  ∀ y z : Y, Eligible S y → Eligible S z → y = z"
        ),
    }
    observation = {
        "name": "Skel.Observation",
        "kind": "structure",
        "module": "Skel.Defs",
        "range": [15, 18],
        "signature": "Skel.Observation (Y : Type) : Type",
        "semantic_schema": "autoform-lean-expr/v2",
        "semantic": _semantic({"type": {"sort": {"zero": None}}, "constructors": []}),
        "depends": [],
        "source": (
            "/-- A structure, to check inductive handling. -/\n"
            "structure Observation (Y : Type) where\n"
            "  admits : Y → Prop\n"
            "  nonempty : ∃ y, admits y"
        ),
    }
    records = [
        "some unrelated line from Lean",
        _record(
            "Skel.observation_determined",
            found=True,
            kind="theorem",
            module="Skel.Main",
            range=[14, 17],
            signature="Skel.observation_determined {Y : Type} (o : Skel.Observation Y) :\n  ∃ y, o.admits y",
            semantic_schema="autoform-lean-expr/v2",
            semantic=_semantic({"type": {"sort": {"zero": None}}}),
            lean_version="4.32.2",
            source=None,
            statement_source=None,
            depends=["Skel.NonAmbiguous", "Skel.Observation"],
            # Deliberately out of dependency order: the report must sort them.
            trusted=[non_ambiguous, observation, eligible],
            assumed=["Mathlib.Fake"],
            assumed_semantics=[["Mathlib.Fake", _semantic({"type": {"sort": {"zero": None}}})]],
            boundary_modules=[["Mathlib.Fake", "olean", "Skel/Defs.lean"]],
            axioms=["sorryAx"],
            axiom_semantics=[["sorryAx", _semantic({"type": {"sort": {"zero": None}}})]],
        ),
    ]
    if include_ghost:
        records.append(_record("Skel.ghost", found=False))
    return "\n".join(records)


def _fake_found_record() -> dict[str, object]:
    line = next(line for line in _fake_probe_output().splitlines() if line.startswith(PROBE_MARKER))
    return json.loads(line[len(PROBE_MARKER) :])


# --------------------------------------------------------------------------- #
# The probe program
# --------------------------------------------------------------------------- #


def test_probe_spells_names_without_trusting_lean_to_parse_them() -> None:
    probe = render_probe(
        imports=("Skel.Main", "Skel.Defs", "Skel.Main"),
        roots=("Skel.observation_determined",),
        project_roots=("Skel",),
    )

    assert probe.startswith("import Skel.Defs\nimport Skel.Main\n")
    assert 'Name.str (Name.str (Name.anonymous) "Skel") "observation_determined"' in probe
    assert f'"{PROBE_MARKER}' in probe
    assert 'Name.str (Name.anonymous) "Init"' in probe
    assert "info.fromClass" in probe


def test_probe_transports_quoted_and_numeric_name_components_structurally() -> None:
    probe = render_probe(
        imports=("Skel.Main",),
        roots=("Skel.«quoted.name with space».2",),
        project_roots=("Skel",),
    )

    assert '"Skel.«quoted.name with space».2"' in probe
    assert 'Name.str (Name.str (Name.anonymous) "Skel") "quoted.name with space"' in probe
    assert "Name.num (Name.str" in probe


def test_probe_refuses_to_render_nothing() -> None:
    with pytest.raises(SkeletonError):
        render_probe(imports=("Skel",), roots=(), project_roots=("Skel",))
    with pytest.raises(SkeletonError):
        render_probe(imports=(), roots=("Skel.x",), project_roots=("Skel",))


def test_probe_refuses_stale_artifacts_before_executing_lean(tmp_path: Path, monkeypatch) -> None:
    calls: list[list[str]] = []
    (tmp_path / "lake-manifest.json").write_text("{}\n", encoding="utf-8")

    def fake_run(command, **kwargs):
        calls.append(command)
        return subprocess.CompletedProcess(command, 3, stdout="target is out-of-date", stderr="")

    monkeypatch.setattr("autoform_cli.skeleton.shutil.which", lambda executable: "/bin/lake")
    monkeypatch.setattr("autoform_cli.skeleton._run_bounded_command", fake_run)
    probe = render_probe(imports=("Skel.Main",), roots=("Skel.x",), project_roots=("Skel",))

    with pytest.raises(SkeletonError, match="build artifacts are stale"):
        run_probe(probe, tmp_path)

    assert calls == [["/bin/lake", "--rehash", "--no-build", "build", "Skel.Main"]]


def test_bounded_command_rejects_excess_output(tmp_path: Path) -> None:
    with pytest.raises(SkeletonError, match="1024-byte output limit"):
        _run_bounded_command(
            [sys.executable, "-c", "import os; os.write(1, b'x' * 4096)"],
            cwd=tmp_path,
            timeout=10,
            context="test command",
            output_limit=1024,
        )


def test_bounded_command_caps_stdout_and_stderr_together(tmp_path: Path) -> None:
    program = "import os; os.write(1, b'x' * 700); os.write(2, b'y' * 700)"
    with pytest.raises(SkeletonError, match="1024-byte output limit"):
        _run_bounded_command(
            [sys.executable, "-c", program],
            cwd=tmp_path,
            timeout=10,
            context="test command",
            output_limit=1024,
        )


def test_bounded_command_rejects_invalid_utf8(tmp_path: Path) -> None:
    with pytest.raises(SkeletonError, match="invalid UTF-8"):
        _run_bounded_command(
            [sys.executable, "-c", "import os; os.write(1, b'\\xff')"],
            cwd=tmp_path,
            timeout=10,
            context="test command",
        )


def test_bounded_command_timeout_kills_descendants(tmp_path: Path) -> None:
    child_pid = tmp_path / "child.pid"
    program = (
        "import pathlib, subprocess, sys, time; "
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)']); "
        f"pathlib.Path({str(child_pid)!r}).write_text(str(child.pid)); "
        "time.sleep(30)"
    )

    with pytest.raises(SkeletonError, match="timed out"):
        _run_bounded_command(
            [sys.executable, "-c", program],
            cwd=tmp_path,
            timeout=2,
            context="test command",
        )

    pid = int(child_pid.read_text(encoding="utf-8"))
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        try:
            child = psutil.Process(pid)
            if not child.is_running() or child.status() == psutil.STATUS_ZOMBIE:
                break
        except psutil.NoSuchProcess:
            break
        time.sleep(0.01)
    else:
        pytest.fail(f"descendant process {pid} survived command timeout")


def test_bounded_command_rejects_a_successful_parent_with_a_live_descendant(
    tmp_path: Path,
) -> None:
    child_pid = tmp_path / "child.pid"
    program = (
        "import pathlib, subprocess, sys; "
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'], "
        "stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
        f"pathlib.Path({str(child_pid)!r}).write_text(str(child.pid))"
    )

    with pytest.raises(SkeletonError, match="descendant processes"):
        _run_bounded_command(
            [sys.executable, "-c", program],
            cwd=tmp_path,
            timeout=10,
            context="test command",
        )
    pid = int(child_pid.read_text(encoding="utf-8"))
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        try:
            child = psutil.Process(pid)
            if not child.is_running() or child.status() == psutil.STATUS_ZOMBIE:
                break
        except psutil.NoSuchProcess:
            break
        time.sleep(0.01)
    else:
        pytest.fail(f"descendant process {pid} survived successful parent exit")


@pytest.mark.skipif(os.name != "posix", reason="detached-session assertion is POSIX-specific")
def test_bounded_command_finds_a_descendant_that_escapes_its_process_group(
    tmp_path: Path,
) -> None:
    child_pid = tmp_path / "detached-child.pid"
    child_program = (
        "import os, pathlib, time; os.setsid(); "
        f"pathlib.Path({str(child_pid)!r}).write_text(str(os.getpid())); time.sleep(30)"
    )
    parent_program = (
        "import subprocess, sys; "
        f"subprocess.Popen([sys.executable, '-c', {child_program!r}], "
        "stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)"
    )

    with pytest.raises(SkeletonError, match="descendant processes"):
        _run_bounded_command(
            [sys.executable, "-c", parent_program],
            cwd=tmp_path,
            timeout=10,
            context="test command",
        )

    pid = int(child_pid.read_text(encoding="utf-8"))
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        try:
            child = psutil.Process(pid)
            if not child.is_running() or child.status() == psutil.STATUS_ZOMBIE:
                break
        except psutil.NoSuchProcess:
            break
        time.sleep(0.01)
    else:
        pytest.fail(f"detached descendant process {pid} survived cleanup")


def test_bounded_command_interruption_kills_the_process(tmp_path: Path, monkeypatch) -> None:
    process_pid = tmp_path / "process.pid"
    program = (
        "import os, pathlib, time; "
        f"pathlib.Path({str(process_pid)!r}).write_text(str(os.getpid())); "
        "time.sleep(30)"
    )
    monotonic = time.monotonic
    calls = 0

    def interrupt_after_start() -> float:
        nonlocal calls
        calls += 1
        if calls == 1:
            return monotonic()
        deadline = monotonic() + 5
        while not process_pid.exists() and monotonic() < deadline:
            time.sleep(0.01)
        raise KeyboardInterrupt

    monkeypatch.setattr("autoform_cli.skeleton.time.monotonic", interrupt_after_start)

    with pytest.raises(KeyboardInterrupt) as interrupted:
        _run_bounded_command(
            [sys.executable, "-c", program],
            cwd=tmp_path,
            timeout=10,
            context="test command",
        )

    pid = int(process_pid.read_text(encoding="utf-8"))
    deadline = monotonic() + 5
    while psutil.pid_exists(pid) and monotonic() < deadline:
        time.sleep(0.01)
    assert not psutil.pid_exists(pid)
    assert interrupted.type is KeyboardInterrupt


def test_bounded_command_cleanup_reserves_time_and_reuses_final_deadline(
    tmp_path: Path, monkeypatch
) -> None:
    deadlines: list[float] = []

    def report_stuck_readers(readers, *, deadline: float) -> bool:
        deadlines.append(deadline)
        _join_readers(readers, deadline=deadline)
        return False

    monkeypatch.setattr("autoform_cli.skeleton._join_readers", report_stuck_readers)

    with pytest.raises(SkeletonError, match="output pipes open"):
        _run_bounded_command(
            [sys.executable, "-c", "pass"],
            cwd=tmp_path,
            timeout=10,
            context="test command",
        )

    assert len(deadlines) == 3
    assert deadlines[0] < deadlines[1]
    assert deadlines[1] == deadlines[2]


def test_probe_freshness_and_execution_share_one_deadline(tmp_path: Path, monkeypatch) -> None:
    (tmp_path / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    calls: list[float] = []

    def fake_run(command, **kwargs):
        calls.append(kwargs["timeout"])
        return subprocess.CompletedProcess(command, 0, stdout="probe output", stderr="")

    times = iter((100.0, 101.0, 104.0))
    monkeypatch.setattr("autoform_cli.skeleton.shutil.which", lambda executable: "/bin/lake")
    monkeypatch.setattr("autoform_cli.skeleton._run_bounded_command", fake_run)
    monkeypatch.setattr("autoform_cli.skeleton.time.monotonic", lambda: next(times))
    probe = render_probe(imports=("Skel.Main",), roots=("Skel.x",), project_roots=("Skel",))

    assert run_probe(probe, tmp_path, timeout=10) == "probe output"
    assert calls == [9.0, 6.0]


def test_probe_requires_an_existing_lake_manifest(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr("autoform_cli.skeleton.shutil.which", lambda executable: "/bin/lake")
    probe = render_probe(imports=("Skel.Main",), roots=("Skel.x",), project_roots=("Skel",))

    with pytest.raises(SkeletonError, match="lake-manifest.json is missing"):
        run_probe(probe, tmp_path)


def test_parse_probe_output_keys_records_by_root_and_ignores_noise() -> None:
    records = parse_probe_output(_fake_probe_output(include_ghost=True))

    assert set(records) == {"Skel.observation_determined", "Skel.ghost"}
    assert records["Skel.ghost"] == {"root": "Skel.ghost", "found": False}


def test_parse_probe_output_rejects_malformed_records() -> None:
    with pytest.raises(SkeletonError):
        parse_probe_output(PROBE_MARKER + "{not json")
    with pytest.raises(SkeletonError):
        parse_probe_output(PROBE_MARKER + '{"found": true}')


def test_parse_probe_output_rejects_wrong_types_duplicates_and_unrequested_roots() -> None:
    with pytest.raises(SkeletonError, match="non-boolean found"):
        parse_probe_output(_record("Skel.ghost", found="false"))

    line = next(line for line in _fake_probe_output().splitlines() if line.startswith(PROBE_MARKER))
    with pytest.raises(SkeletonError, match="duplicate records"):
        parse_probe_output("\n".join([line, line]))
    with pytest.raises(SkeletonError, match="unrequested root"):
        parse_probe_output(line, expected_roots=("Skel.somewhere_else",))


def test_parse_probe_output_rejects_incomplete_semantic_records() -> None:
    record = _fake_found_record()
    record["semantic_schema"] = "unknown"
    with pytest.raises(SkeletonError, match="unsupported semantic schema"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))

    record = _fake_found_record()
    record["semantic"] = "not JSON"
    with pytest.raises(SkeletonError, match="invalid elaborated semantic material"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))

    record = _fake_found_record()
    semantic = json.loads(str(record["semantic"]))
    semantic["generated"] = [
        {"name": "ambiguous.display.name", "material": semantic["root"]}
    ]
    record["semantic"] = json.dumps(semantic)
    with pytest.raises(SkeletonError, match="invalid elaborated semantic material"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))

    record = _fake_found_record()
    trusted = record["trusted"]
    assert isinstance(trusted, list) and isinstance(trusted[0], dict)
    trusted[0]["depends"] = [False]
    with pytest.raises(SkeletonError, match="invalid depends"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))

    record = _fake_found_record()
    trusted = record["trusted"]
    assert isinstance(trusted, list) and isinstance(trusted[0], dict)
    trusted[0]["source"] = None
    with pytest.raises(SkeletonError, match="omitted required source"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))

    record = _fake_found_record()
    record["source"] = "theorem t : True := by trivial"
    with pytest.raises(SkeletonError, match="proof-bearing source"):
        parse_probe_output(PROBE_MARKER + json.dumps(record))


# --------------------------------------------------------------------------- #
# Project layout
# --------------------------------------------------------------------------- #


def test_libraries_and_modules_follow_the_lake_source_directory(tmp_path: Path) -> None:
    project = _project(tmp_path, src_dir="src")

    libraries = lean_libraries(project)

    assert [library.name for library in libraries] == ["Skel"]
    assert libraries[0].src_dir == (project / "src").resolve()
    assert libraries[0].roots == ("Skel",)
    assert module_of(project / "src" / "Skel" / "Defs.lean", libraries) == "Skel.Defs"
    assert module_of(project / "lakefile.toml", libraries) is None
    assert path_of("Skel.Defs", libraries, project) == "src/Skel/Defs.lean"
    assert path_of("Skel.Missing", libraries, project) is None


def test_a_package_without_library_targets_is_its_own_library(tmp_path: Path) -> None:
    project = tmp_path / "project"
    project.mkdir()
    (project / "lakefile.toml").write_text('name = "Solo"\n', encoding="utf-8")

    (library,) = lean_libraries(project)

    assert (library.name, library.roots) == ("Solo", ("Solo",))
    assert library.src_dir == project.resolve()


def test_a_project_without_a_lakefile_is_refused(tmp_path: Path) -> None:
    with pytest.raises(SkeletonError):
        lean_libraries(tmp_path)


@pytest.mark.skipif(os.name != "posix", reason="named pipes are POSIX-specific")
def test_lake_configuration_snapshot_rejects_a_named_pipe_without_blocking(tmp_path: Path) -> None:
    os.mkfifo(tmp_path / "lakefile.toml")

    with pytest.raises(SkeletonError, match="not a regular file"):
        lean_libraries(tmp_path)


def test_lake_configuration_snapshot_uses_content_not_file_identity(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    fstat = os.fstat
    calls = 0

    def unstable_file_identity(descriptor: int) -> os.stat_result:
        nonlocal calls
        calls += 1
        values = list(fstat(descriptor))
        values[1] += calls
        return os.stat_result(values)

    monkeypatch.setattr("autoform_cli.skeleton.os.fstat", unstable_file_identity)

    (library,) = lean_libraries(project)

    assert library.name == "Skel"


def test_lake_configuration_snapshot_rejects_content_changed_between_reads(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    lakefile = project / "lakefile.toml"
    open_file = os.open
    reads = 0

    def change_before_second_read(path, flags, *args):
        nonlocal reads
        if Path(path) == lakefile:
            reads += 1
            if reads == 2:
                lakefile.write_text('name = "Changed"\n', encoding="utf-8")
        return open_file(path, flags, *args)

    monkeypatch.setattr("autoform_cli.skeleton.os.open", change_before_second_read)

    with pytest.raises(SkeletonError, match="changed while it was read"):
        lean_libraries(project)


# --------------------------------------------------------------------------- #
# Extraction against a fake probe
# --------------------------------------------------------------------------- #


def test_extraction_orders_the_skeleton_and_locates_every_source(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    probes: list[str] = []

    def runner(probe: str, lean_root: Path) -> str:
        probes.append(probe)
        assert lean_root == project.resolve()
        return _fake_probe_output()

    report = extract_skeletons(blueprint, lean_root=project, runner=runner)

    assert report.clean
    assert len(probes) == 1 and "import Skel.Main" in probes[0]
    (node,) = report.nodes
    assert node.node_id == "basics/determined"
    assert node.article_path == "roadmap/basics/determined.md"
    (declaration,) = node.declarations
    assert declaration.path == "Skel/Main.lean"
    assert (declaration.start_line, declaration.end_line) == (14, 17)
    assert declaration.axioms == ("sorryAx",)
    assert declaration.assumed == ("Mathlib.Fake",)
    # Each trusted declaration is read after what it rests on; ties by name.
    assert [item.name for item in declaration.trusted] == [
        "Skel.Eligible",
        "Skel.NonAmbiguous",
        "Skel.Observation",
    ]
    assert declaration.trusted[1].path == "Skel/Defs.lean"
    # Two signature lines plus spans of 2, 3, and 4 source lines.
    assert declaration.skeleton_lines == 2 + 2 + 3 + 4
    assert declaration.declaration_lines == 4


def test_skeleton_hash_uses_elaborated_semantics_not_source_formatting(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda probe, root: _fake_probe_output())
    declaration = report.nodes[0].declarations[0]

    presentation_only = replace(declaration, signature="differently formatted", statement="different spelling")
    semantic_change = replace(declaration, semantic=declaration.semantic + " changed")
    assumed_change = replace(
        declaration,
        assumed_semantics=((declaration.assumed[0], "changed external definition"),),
    )
    axiom_change = replace(
        declaration,
        axiom_semantics=((declaration.axioms[0], "changed axiom type"),),
    )
    module, file_kind, _ = declaration.boundary_modules[0]
    module_change = replace(
        declaration,
        boundary_modules=((module, file_kind, "sha256:" + "0" * 64),),
    )
    hidden_assumption = replace(declaration, assumed=())

    assert presentation_only.hash == declaration.hash
    assert presentation_only.evidence_hash != declaration.evidence_hash
    assert semantic_change.hash != declaration.hash
    assert assumed_change.hash != declaration.hash
    assert axiom_change.hash != declaration.hash
    assert module_change.hash != declaration.hash
    assert hidden_assumption.hash != declaration.hash


def test_assumed_module_identity_rejects_a_concurrent_rebuild(tmp_path: Path) -> None:
    artifact = tmp_path / "External.olean"
    artifact.write_bytes(b"old")
    started = time.time_ns()
    artifact.write_bytes(b"new")

    with pytest.raises(SkeletonError, match="changed during skeleton extraction"):
        _hash_module_files(
            [["External", "olean", str(artifact)]],
            lean_root=tmp_path,
            cache={},
            snapshot_started_ns=started,
        )


def test_trusted_theorem_source_never_exposes_its_proof(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    record = _fake_found_record()
    trusted = record["trusted"]
    assert isinstance(trusted, list)
    trusted.append(
        {
            "name": "Skel.eligible_of",
            "kind": "theorem",
            "module": "Skel.Defs",
            "range": [12, 13],
            "signature": "Skel.eligible_of {Y : Type} (S : Y → Prop) (y : Y) (h : S y) : Skel.Eligible S y",
            "semantic_schema": "autoform-lean-expr/v2",
            "semantic": _semantic({"type": {"sort": {"zero": None}}}),
            "depends": ["Skel.Eligible"],
            "source": None,
        }
    )
    output = PROBE_MARKER + json.dumps(record)

    report = extract_skeletons(blueprint, lean_root=project, runner=lambda probe, root: output)
    theorem = next(item for item in report.nodes[0].declarations[0].trusted if item.name == "Skel.eligible_of")

    assert theorem.source is None
    assert ":= h" not in report.nodes[0].declarations[0].blind_text()
    assert ":= h" not in format_report(report, lean_root=project)


def test_extraction_reports_names_the_sources_and_the_environment_lack(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(
        tmp_path,
        lean={
            "determined": "Skel.observation_determined",
            "phantom": "Skel.doesNotExist",
            "ghost": "Skel.ghost",
        },
    )
    # `Skel.ghost` is lexically present so the probe is asked about it, but the
    # fake environment does not contain it, as after an unbuilt edit.
    main_file = project / "Skel" / "Main.lean"
    main_file.write_text(
        main_file.read_text(encoding="utf-8") + "\nnamespace Skel\ntheorem ghost : True := trivial\nend Skel\n",
        encoding="utf-8",
    )

    report = extract_skeletons(
        blueprint, lean_root=project, runner=lambda probe, root: _fake_probe_output(include_ghost=True)
    )

    assert not report.clean
    assert report.unresolved == (
        "basics/ghost: Skel.ghost is not in the built environment; run `lake build`",
        "basics/phantom: declaration not found in the Lean sources: Skel.doesNotExist",
    )
    assert [node.node_id for node in report.nodes] == ["basics/determined", "basics/ghost", "basics/phantom"]
    assert report.nodes[1].declarations == ()


def test_extraction_never_runs_lean_when_nothing_resolves(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"phantom": "Skel.doesNotExist"})

    def runner(probe: str, lean_root: Path) -> str:
        raise AssertionError("the probe must not run")

    report = extract_skeletons(blueprint, lean_root=project, runner=runner)

    assert report.unresolved == ("basics/phantom: declaration not found in the Lean sources: Skel.doesNotExist",)


def test_default_extraction_rejects_sources_changed_during_probe(tmp_path: Path, monkeypatch) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})

    def changing_probe(probe: str, lean_root: Path) -> str:
        source = lean_root / "Skel" / "Defs.lean"
        source.write_text(source.read_text(encoding="utf-8") + "\n-- concurrent edit\n", encoding="utf-8")
        return _fake_probe_output()

    monkeypatch.setattr("autoform_cli.skeleton.run_probe", changing_probe)

    with pytest.raises(SkeletonError, match="changed during skeleton extraction"):
        extract_skeletons(blueprint, lean_root=project)


def test_custom_runner_rejects_sources_changed_during_probe(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})

    def changing_runner(probe: str, lean_root: Path) -> str:
        source = lean_root / "Skel" / "Main.lean"
        source.write_text(
            source.read_text(encoding="utf-8") + "\n-- concurrent edit\n",
            encoding="utf-8",
        )
        return _fake_probe_output()

    with pytest.raises(SkeletonError, match="Lean sources changed"):
        extract_skeletons(blueprint, lean_root=project, runner=changing_runner)


def test_extraction_rejects_a_blueprint_changed_during_probe(tmp_path: Path, monkeypatch) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    article = blueprint / "roadmap" / "basics" / "determined.md"

    def changing_probe(probe: str, lean_root: Path) -> str:
        article.write_text(article.read_text(encoding="utf-8") + "\nChanged.\n", encoding="utf-8")
        return _fake_probe_output()

    monkeypatch.setattr("autoform_cli.skeleton.run_probe", changing_probe)

    with pytest.raises(SkeletonError, match="blueprint changed"):
        extract_skeletons(blueprint, lean_root=project)


def test_extraction_rejects_a_passage_changed_during_probe(tmp_path: Path, monkeypatch) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    source = blueprint / "sources" / "book.tex"
    source.parent.mkdir()
    source.write_text("before\n", encoding="utf-8")
    article = blueprint / "roadmap" / "basics" / "determined.md"
    article.write_text(
        article.read_text(encoding="utf-8").replace(
            "## Depends on",
            "## Sources\n\n- [book](../../sources/book.tex#L1-L1)\n\n## Depends on",
        ),
        encoding="utf-8",
    )

    def changing_probe(probe: str, lean_root: Path) -> str:
        source.write_text("after\n", encoding="utf-8")
        return _fake_probe_output()

    monkeypatch.setattr("autoform_cli.skeleton.run_probe", changing_probe)

    with pytest.raises(SkeletonError, match="source passage changed"):
        extract_skeletons(blueprint, lean_root=project)


def test_extraction_rejects_lake_configuration_changed_during_probe(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})

    def changing_probe(probe: str, lean_root: Path) -> str:
        lakefile = lean_root / "lakefile.toml"
        lakefile.write_text(lakefile.read_text(encoding="utf-8") + "\n# changed\n", encoding="utf-8")
        return _fake_probe_output()

    monkeypatch.setattr("autoform_cli.skeleton.run_probe", changing_probe)

    with pytest.raises(SkeletonError, match="configuration changed"):
        extract_skeletons(blueprint, lean_root=project)


def test_node_selection_rejects_unknown_articles(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})

    with pytest.raises(SkeletonError) as caught:
        extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: "", node_ids=("basics/nope",))

    assert caught.value.issues == ("unknown article: basics/nope",)


def test_report_round_trips_through_json_deterministically(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())

    first = report.to_json()
    assert first == report.to_json()
    assert json.loads(first)["schema"] == SKELETON_SCHEMA
    assert str(tmp_path) not in first

    path = tmp_path / "skeleton.json"
    path.write_text(first, encoding="utf-8")
    assert load_skeleton_report(path) == report

    path.write_text('{"schema": "something-else"}', encoding="utf-8")
    with pytest.raises(SkeletonError):
        load_skeleton_report(path)

    legacy = report.as_dict()
    legacy["schema"] = "autoform-skeleton/v1"
    path.write_text(json.dumps(legacy), encoding="utf-8")
    with pytest.raises(SkeletonError):
        load_skeleton_report(path)


def test_report_loader_rejects_mismatched_hashes_and_trust_identities(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    path = tmp_path / "skeleton.json"

    payload = report.as_dict()
    payload["nodes"][0]["declarations"][0]["hash"] = "sha256:" + "0" * 64
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(SkeletonError, match="invalid declaration hash"):
        load_skeleton_report(path)

    payload = report.as_dict()
    payload["nodes"][0]["declarations"][0]["statement"] = "theorem t : True := by trivial"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(SkeletonError, match="invalid declaration evidence hash"):
        load_skeleton_report(path)

    payload = report.as_dict()
    payload["nodes"][0]["passage"] = "different source theorem"
    payload["nodes"][0]["passage_locator"] = "sources/book.tex#L1-L1"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(SkeletonError, match="invalid article review hash"):
        load_skeleton_report(path)

    payload = report.as_dict()
    payload["nodes"][0]["declarations"][0]["assumed"] = ["Mathlib.Other"]
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(SkeletonError, match="mismatched assumption semantics"):
        load_skeleton_report(path)

    payload = report.as_dict()
    trusted = payload["nodes"][0]["declarations"][0]["trusted"][0]
    trusted["kind"] = "theorem"
    trusted["semantic"] = _semantic({"type": {"sort": {"zero": None}}})
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(SkeletonError, match="proof-bearing source is forbidden"):
        load_skeleton_report(path)


def test_text_report_quotes_the_sources_a_reader_must_trust(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())

    text = format_report(report, lean_root=project)

    assert text.startswith("== basics/determined · theorem Skel.observation_determined\n")
    assert "   trusts 3 local declarations, 11 lines to read; the declaration itself spans 4 lines · skeleton " in text
    assert "   assumes: Mathlib.Fake\n" in text
    assert "   axioms: sorryAx\n" in text
    assert "   -- def Skel.Eligible  (Skel/Defs.lean:5-6)\n" in text
    assert "   def Eligible (S : Y → Prop) (y : Y) : Prop := S y\n" in text
    assert "   structure Observation (Y : Type) where\n" in text
    # The elaborated signature restores what `variable` binders leave implicit.
    assert "   -- Skel.NonAmbiguous {Y : Type} (S : Y → Prop) : Prop\n" in text
    # The quoted source travels inside the report, so no Lean tree is needed to print it.
    assert "   def Eligible (S : Y → Prop) (y : Y) : Prop := S y\n" in format_report(report)


def test_cli_writes_the_artifact_and_fails_on_unresolved_names(tmp_path: Path, capsys, monkeypatch) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(
        tmp_path,
        lean={"determined": "Skel.observation_determined", "phantom": "Skel.doesNotExist"},
    )
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    output = tmp_path / "out" / "skeleton.json"

    assert main(["skeleton", str(blueprint), "--lean-root", str(project), "--output", str(output)]) == 1

    out = capsys.readouterr().out
    assert out.splitlines() == [
        f"{output}: 1 skeleton(s) for 2 article(s)",
        "error: basics/phantom: declaration not found in the Lean sources: Skel.doesNotExist",
    ]
    assert load_skeleton_report(output).nodes[0].node_id == "basics/determined"

    assert main(["skeleton", str(blueprint), "--lean-root", str(project), "--node", "basics/determined", "--json"]) == 0
    assert json.loads(capsys.readouterr().out)["unresolved"] == []


def test_cli_reports_extraction_failures_on_stderr(tmp_path: Path, capsys) -> None:
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})

    assert main(["skeleton", str(blueprint), "--lean-root", str(tmp_path / "nowhere")]) == 2

    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err.startswith("error: no lakefile.toml or lakefile.lean in ")


def test_cli_reports_an_invalid_report_output_without_a_traceback(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    output = tmp_path / "skeleton.json"
    output.mkdir()

    assert main(
        ["skeleton", str(blueprint), "--lean-root", str(project), "--output", str(output)]
    ) == 2

    captured = capsys.readouterr()
    assert captured.out == ""
    assert "report output exists and is not a regular file" in captured.err


def test_cli_keeps_json_stdout_machine_readable_with_packets(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"

    assert main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
            "--json",
        ]
    ) == 0

    captured = capsys.readouterr()
    assert json.loads(captured.out)["schema"] == SKELETON_SCHEMA
    assert "blind packet(s) written" in captured.err


def test_cli_rejects_passages_without_packets(tmp_path: Path, capsys) -> None:
    assert main(
        [
            "skeleton",
            str(tmp_path / "missing-blueprint"),
            "--lean-root",
            str(tmp_path / "missing-project"),
            "--passages",
            str(tmp_path / "passages"),
        ]
    ) == 2

    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == "error: --passages requires --packets\n"


def test_cli_reports_unsafe_packet_output_without_a_traceback(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    packets.mkdir()
    (packets / "keep.txt").write_text("mine\n", encoding="utf-8")

    assert main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
        ]
    ) == 2

    captured = capsys.readouterr()
    assert captured.out == ""
    assert "refusing to overwrite non-Autoform packet output" in captured.err


def test_cli_rejects_a_report_path_inside_the_packet_tree(tmp_path: Path, capsys) -> None:
    packets = tmp_path / "packets"
    assert main(
        [
            "skeleton",
            str(tmp_path / "blueprint"),
            "--lean-root",
            str(tmp_path / "project"),
            "--packets",
            str(packets),
            "--output",
            str(packets / "manifest.json"),
        ]
    ) == 2

    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == "error: --output must be disjoint from packet and passage directories\n"


def test_cli_publishes_report_and_packet_trees_together(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    output = tmp_path / "skeleton.json"
    output.write_text("old report\n", encoding="utf-8")

    result = main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
            "--passages",
            str(passages),
            "--output",
            str(output),
        ]
    )

    assert result == 0
    assert (packets / PACKET_MANIFEST).is_file()
    assert (passages / PACKET_MANIFEST).is_file()
    assert load_skeleton_report(output).clean
    assert list(tmp_path.glob(".*.autoform-*")) == []
    assert capsys.readouterr().err == ""


def test_cli_does_not_publish_packets_when_report_staging_fails(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    output = tmp_path / "skeleton.json"

    def fail_report_stage(report: SkeletonReport, destination: Path):
        raise OSError("simulated report staging failure")

    monkeypatch.setattr("autoform_cli.skeleton._stage_report_output", fail_report_stage)

    result = main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
            "--passages",
            str(passages),
            "--output",
            str(output),
        ]
    )

    assert result == 2
    assert not packets.exists()
    assert not passages.exists()
    assert not output.exists()
    assert list(tmp_path.glob(".*.autoform-stage-*")) == []
    assert "simulated report staging failure" in capsys.readouterr().err


def test_cli_rolls_back_packet_trees_when_report_commit_fails(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    output = tmp_path / "skeleton.json"
    install_output = _install_output

    def fail_report_install(source: str | Path, destination: str | Path) -> None:
        source_path = Path(source)
        if "autoform-stage" in source_path.name and Path(destination) == output:
            raise OSError("simulated report commit failure")
        install_output(source_path, Path(destination))

    monkeypatch.setattr("autoform_cli.skeleton._install_output", fail_report_install)

    result = main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
            "--passages",
            str(passages),
            "--output",
            str(output),
        ]
    )

    assert result == 2
    assert not packets.exists()
    assert not passages.exists()
    assert not output.exists()
    assert list(tmp_path.glob(".*.autoform-*")) == []
    assert "simulated report commit failure" in capsys.readouterr().err


def test_cli_rolls_back_packet_trees_and_report_when_interrupted_after_report_install(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    output = tmp_path / "skeleton.json"
    output.write_text("old report\n", encoding="utf-8")
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    (passages / "old-marker").write_text("old passages\n", encoding="utf-8")
    install_output = _install_output

    def interrupt_after_report_install(source: str | Path, destination: str | Path) -> None:
        install_output(Path(source), Path(destination))
        if "autoform-stage" in Path(source).name and Path(destination) == output:
            raise KeyboardInterrupt

    monkeypatch.setattr(
        "autoform_cli.skeleton._install_output", interrupt_after_report_install
    )

    with pytest.raises(KeyboardInterrupt):
        main(
            [
                "skeleton",
                str(blueprint),
                "--lean-root",
                str(project),
                "--packets",
                str(packets),
                "--passages",
                str(passages),
                "--output",
                str(output),
            ]
        )

    assert (packets / "old-marker").read_text(encoding="utf-8") == "old packets\n"
    assert (passages / "old-marker").read_text(encoding="utf-8") == "old passages\n"
    assert output.read_text(encoding="utf-8") == "old report\n"
    assert list(tmp_path.glob(".*.autoform-*")) == []


def test_report_publication_preserves_a_concurrent_replacement_before_install(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    output = tmp_path / "skeleton.json"
    output.write_text("old report\n", encoding="utf-8")
    install_output = _install_output

    def replace_before_install(stage: Path, destination: Path) -> None:
        if destination == output:
            output.write_text("concurrent report\n", encoding="utf-8")
        install_output(stage, destination)

    monkeypatch.setattr("autoform_cli.skeleton._install_output", replace_before_install)

    with pytest.raises(SkeletonError, match="published output changed during rollback"):
        write_skeleton_report(report, output)

    assert output.read_text(encoding="utf-8") == "concurrent report\n"
    backups = list(tmp_path.glob(".skeleton.json.autoform-backup-*"))
    assert len(backups) == 1
    assert backups[0].read_text(encoding="utf-8") == "old report\n"


def test_report_publication_rolls_back_when_interrupted_after_exclusive_link(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    output = tmp_path / "skeleton.json"
    output.write_text("old report\n", encoding="utf-8")
    link = os.link

    def interrupt_after_link(source: str | Path, destination: str | Path) -> None:
        link(source, destination)
        if "autoform-stage" in Path(source).name and Path(destination) == output:
            raise KeyboardInterrupt

    monkeypatch.setattr("autoform_cli.skeleton.os.link", interrupt_after_link)

    with pytest.raises(KeyboardInterrupt):
        write_skeleton_report(report, output)

    assert output.read_text(encoding="utf-8") == "old report\n"
    assert list(tmp_path.glob(".*.autoform-*")) == []


def test_cli_refuses_a_symlink_report_without_publishing_packets(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    report_target = tmp_path / "report-target.json"
    report_target.write_text("keep me\n", encoding="utf-8")
    output = tmp_path / "skeleton.json"
    output.symlink_to(report_target)

    result = main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--packets",
            str(packets),
            "--passages",
            str(passages),
            "--output",
            str(output),
        ]
    )

    assert result == 2
    assert not packets.exists()
    assert not passages.exists()
    assert output.is_symlink()
    assert report_target.read_text(encoding="utf-8") == "keep me\n"
    assert "refusing symlink report output" in capsys.readouterr().err


# --------------------------------------------------------------------------- #
# The real probe
# --------------------------------------------------------------------------- #


def _lean_toolchain_available() -> bool:
    """Whether the fixture can be built here without downloading a toolchain."""

    if shutil.which("lake") is None:
        return False
    elan = shutil.which("elan")
    if elan is None:
        return True
    pinned = (_FIXTURE / "lean-toolchain").read_text(encoding="utf-8").strip()
    try:
        listed = subprocess.run([elan, "toolchain", "list"], capture_output=True, text=True, timeout=30, check=False)
    except (OSError, subprocess.SubprocessError):
        return False
    return any(line.split()[:1] == [pinned] for line in listed.stdout.splitlines())


@pytest.mark.skipif(not _lean_toolchain_available(), reason="needs lake and the fixture's Lean toolchain")
def test_the_probe_reads_a_built_project(tmp_path: Path) -> None:
    project = _project(tmp_path)
    build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=600, check=False)
    assert build.returncode == 0, build.stderr
    blueprint = _blueprint(
        tmp_path,
        lean={
            "determined": "Skel.observation_determined",
            "heavy": "Skel.heavy_of_weight",
            "notation": "Skel.heavy_of_notation",
            "supervision": "Skel.supervision_nonAmbiguous, Skel.supervision",
        },
    )

    report = extract_skeletons(blueprint, lean_root=project)

    assert report.clean
    determined = report.nodes[0].declarations[0]
    # Scoped notation from a namespace the file opens still parses, and a cast
    # is printed with the type it lands in.
    notation = next(d for n in report.nodes for d in n.declarations if d.name == "Skel.heavy_of_notation")
    assert notation.statement is not None
    assert notation.statement.rstrip().endswith("Skel.heavy (1 : Nat)")
    assert "(↑1 : Int)" in notation.signature or "(↑(1 : Nat) : Int)" in notation.signature
    # The statement as written is cut before the proof by Lean's parser.
    assert determined.statement is not None
    assert determined.statement.startswith("/-- Uses a structure in its statement")
    assert determined.statement.rstrip().endswith("∀ z, o.admits z → z = y")
    assert ":=" not in determined.statement and "sorry" not in determined.statement.split("-/")[-1]
    blind = determined.blind_text()
    assert "-- as written:" in blind and ":= by" not in blind and "sorry in its proof" not in blind
    # The statement rests on two definitions and a structure. The helper lemma
    # the proof uses, and the structure's generated companions, never appear.
    assert [(item.name, item.kind) for item in determined.trusted] == [
        ("Skel.Eligible", "def"),
        ("Skel.NonAmbiguous", "def"),
        ("Skel.Observation", "structure"),
    ]
    assert determined.axioms == ("sorryAx",)
    assert determined.assumed == ()
    assert determined.signature.startswith("Skel.observation_determined {Y : Type} (o : Skel.Observation Y)")
    assert determined.trusted[2].start_line == 15 and determined.trusted[2].end_line == 18

    heavy = report.nodes[1].declarations[0]
    # A local class reached through its projection is trusted once, as the class.
    assert [(item.name, item.kind) for item in heavy.trusted] == [("Skel.HasWeight", "class"), ("Skel.heavy", "def")]

    supervision, definition = next(n for n in report.nodes if n.node_id.endswith("/supervision")).declarations
    assert [item.name for item in supervision.trusted] == ["Skel.Eligible", "Skel.NonAmbiguous", "Skel.supervision"]
    assert supervision.axioms == ()
    assert definition.kind == "def" and definition.trusted == ()

    source = project / "Skel" / "Main.lean"
    source.write_text(
        source.read_text(encoding="utf-8").replace(
            "∃ y, o.admits y ∧ ∀ z, o.admits z → z = y := by",
            "True := by",
        ),
        encoding="utf-8",
    )
    with pytest.raises(SkeletonError, match="build artifacts are stale"):
        extract_skeletons(blueprint, lean_root=project)


@pytest.mark.skipif(not _lean_toolchain_available(), reason="needs lake and the fixture's Lean toolchain")
def test_probe_semantics_cover_elaboration_and_the_full_trust_boundary(tmp_path: Path) -> None:
    project = _project(tmp_path)
    build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=600, check=False)
    assert build.returncode == 0, build.stderr

    roots = (
        "Skel.Semantics.expandedMacro",
        "Skel.Semantics.matchBody",
        "Skel.Semantics.usesOpaque",
        "Skel.Semantics.selectedProposition",
        "Skel.Semantics.usesQuoted",
    )

    def records() -> dict[str, dict[str, object]]:
        probe = render_probe(
            imports=("Skel.Semantics",),
            roots=roots,
            # A dotted Lake root must include this module, but not Skel.Vendor.
            project_roots=("Skel.Semantics",),
        )
        return parse_probe_output(run_probe(probe, project))

    before = records()
    macro = before["Skel.Semantics.expandedMacro"]
    assert macro["semantic_schema"] == "autoform-lean-expr/v2"
    assert set(json.loads(str(macro["semantic"]))["root"]) == {"type", "value"}

    opaque = before["Skel.Semantics.usesOpaque"]
    assert [item["name"] for item in opaque["trusted"]] == [
        "Skel.Semantics.opaqueSeed",
        "Skel.Semantics.opaqueWitness",
    ]
    opaque_item = next(item for item in opaque["trusted"] if item["name"].endswith("opaqueWitness"))
    assert set(json.loads(opaque_item["semantic"])["root"]) == {"type", "value"}

    selected = before["Skel.Semantics.selectedProposition"]
    assert selected["trusted"] == []
    assert selected["assumed"] == ["Vendor.instChoice"]
    assert [item[0] for item in selected["assumed_semantics"]] == [
        "Vendor.instChoice",
    ]
    assert [item[0] for item in selected["boundary_modules"]] == ["Skel.Vendor"]
    before_modules = _hash_module_files(selected["boundary_modules"], lean_root=project, cache={})
    local_probe = render_probe(
        imports=("Skel.Semantics",),
        roots=("Skel.Semantics.selectedProposition",),
        project_roots=("Skel",),
    )
    local_selected = parse_probe_output(run_probe(local_probe, project))[
        "Skel.Semantics.selectedProposition"
    ]
    local_semantics = {item["name"]: item["semantic"] for item in local_selected["trusted"]}
    assert "Vendor.instChoice" in local_semantics
    assert "Vendor.selectedChoice" in local_semantics
    quoted = before["Skel.Semantics.usesQuoted"]
    assert [item["name"] for item in quoted["trusted"]] == ["Skel.Semantics.«quoted.helper»"]

    matched = before["Skel.Semantics.matchBody"]
    assert matched["trusted"] == []
    generated = json.loads(str(matched["semantic"]))["generated"]
    assert len(generated) == 1
    assert isinstance(generated[0]["name"], dict)

    source = project / "Skel" / "Semantics.lean"
    text = source.read_text(encoding="utf-8")
    source.write_text(
        text.replace("| `(semanticMacro) => `(1)", "| `(semanticMacro) => `(2)").replace(
            "  | 0 => 10\n  | n + 1 => n",
            "  | 1 => 10\n  | n => n",
        ),
        encoding="utf-8",
    )
    rebuild = subprocess.run(
        ["lake", "build", "Skel.Semantics"],
        cwd=project,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    assert rebuild.returncode == 0, rebuild.stderr
    changed = records()
    after = changed["Skel.Semantics.expandedMacro"]
    assert after["signature"] == macro["signature"]
    assert after["statement_source"] == macro["statement_source"]
    assert after["semantic"] != macro["semantic"]
    changed_match = changed["Skel.Semantics.matchBody"]
    assert changed_match["signature"] == matched["signature"]
    assert changed_match["semantic"] != matched["semantic"]
    assert changed_match["trusted"] == []

    vendor = project / "Skel" / "Vendor.lean"
    vendor.write_text(
        vendor.read_text(encoding="utf-8").replace("⟨True⟩", "⟨False⟩"),
        encoding="utf-8",
    )
    rebuild = subprocess.run(
        ["lake", "build", "Skel.Semantics"],
        cwd=project,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    assert rebuild.returncode == 0, rebuild.stderr
    changed_instance = records()["Skel.Semantics.selectedProposition"]
    assert changed_instance["semantic"] == selected["semantic"]
    assert changed_instance["assumed"] == selected["assumed"]
    assert changed_instance["assumed_semantics"] == selected["assumed_semantics"]
    assert _hash_module_files(
        changed_instance["boundary_modules"], lean_root=project, cache={}
    ) != before_modules
    changed_local = parse_probe_output(run_probe(local_probe, project))[
        "Skel.Semantics.selectedProposition"
    ]
    changed_local_semantics = {
        item["name"]: item["semantic"] for item in changed_local["trusted"]
    }
    assert changed_local_semantics["Vendor.selectedChoice"] != local_semantics[
        "Vendor.selectedChoice"
    ]


@pytest.mark.skipif(not _lean_toolchain_available(), reason="needs lake and the fixture's Lean toolchain")
def test_axiom_types_are_part_of_the_trust_boundary(tmp_path: Path) -> None:
    project = _project(tmp_path)
    build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=600, check=False)
    assert build.returncode == 0, build.stderr

    external_probe = render_probe(
        imports=("Skel.AxiomUse",),
        roots=("Skel.AxiomUse.result",),
        project_roots=("Skel.AxiomUse",),
    )
    external = parse_probe_output(run_probe(external_probe, project))["Skel.AxiomUse.result"]
    assert external["assumed"] == ["AxiomVendor.P"]
    assert [item[0] for item in external["boundary_modules"]] == ["Skel.AxiomVendor"]
    external_modules = _hash_module_files(external["boundary_modules"], lean_root=project, cache={})

    local_probe = render_probe(
        imports=("Skel.AxiomUse",),
        roots=("Skel.AxiomUse.result",),
        project_roots=("Skel",),
    )
    local = parse_probe_output(run_probe(local_probe, project))["Skel.AxiomUse.result"]
    assert [item["name"] for item in local["trusted"]] == ["AxiomVendor.P"]
    proposition = local["trusted"][0]

    source = project / "Skel" / "AxiomVendor.lean"
    source.write_text(
        source.read_text(encoding="utf-8").replace("def P : Prop := True", "def P : Prop := False"),
        encoding="utf-8",
    )
    rebuild = subprocess.run(
        ["lake", "build", "Skel.AxiomUse"],
        cwd=project,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    assert rebuild.returncode == 0, rebuild.stderr

    changed_external = parse_probe_output(run_probe(external_probe, project))["Skel.AxiomUse.result"]
    assert _hash_module_files(
        changed_external["boundary_modules"], lean_root=project, cache={}
    ) != external_modules
    changed_local = parse_probe_output(run_probe(local_probe, project))["Skel.AxiomUse.result"]
    changed_proposition = changed_local["trusted"][0]
    assert changed_proposition["name"] == proposition["name"]
    assert changed_proposition["semantic"] != proposition["semantic"]


@pytest.mark.skipif(not _lean_toolchain_available(), reason="needs lake and the fixture's Lean toolchain")
def test_statement_parsing_does_not_leak_scoped_notation(tmp_path: Path) -> None:
    project = _project(tmp_path)
    build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=600, check=False)
    assert build.returncode == 0, build.stderr
    probe = render_probe(
        imports=("Skel.ScopedA",),
        roots=("Skel.ScopedA.activatesScope",),
        project_roots=("Skel",),
    )
    probe += """
open Lean Elab Command
run_cmd do
  let _ ← AutoformSkeleton.statementSource `Skel.ScopedA.activatesScope
  let env ← getEnv
  match Parser.runParserCategory env `command
      "example : ⟬marker⟭ = Skel.Semantics.notationMarker := rfl" with
  | .error _ => pure ()
  | .ok _ => throwError "scoped notation escaped statementSource"
"""

    record = parse_probe_output(run_probe(probe, project))["Skel.ScopedA.activatesScope"]
    assert "⟬marker⟭" in record["statement_source"]


# --------------------------------------------------------------------------- #
# Source passages
# --------------------------------------------------------------------------- #


def test_a_line_locator_on_a_source_file_yields_the_passage(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    source = blueprint / "sources" / "book.tex"
    source.parent.mkdir()
    # A form feed inside an earlier line, as `pdftotext` writes between pages,
    # must not count as a line break: locators are what `sed` counts.
    source.write_text("\n".join(f"line {n}" + ("\x0c" if n == 2 else "") for n in range(1, 21)) + "\n", encoding="utf-8")
    article = blueprint / "roadmap" / "basics" / "determined.md"
    article.write_text(
        article.read_text(encoding="utf-8").replace(
            "## Depends on",
            "## Sources\n\n- [notes](../../sources/notes.md)\n- [Theorem 2](../../sources/book.tex#L5-L7)\n\n## Depends on",
        ),
        encoding="utf-8",
    )
    (blueprint / "sources" / "notes.md").write_text("# Notes\n", encoding="utf-8")

    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())

    (node,) = report.nodes
    assert node.passage == "line 5\nline 6\nline 7"
    assert node.passage_locator == "sources/book.tex#L5-L7"
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    assert (passages / "basics" / "determined" / "passage.txt").read_text(encoding="utf-8") == "line 5\nline 6\nline 7\n"
    manifest = json.loads((packets / PACKET_MANIFEST).read_text(encoding="utf-8"))
    assert manifest["packets"][0]["passage"] == "basics/determined/passage.txt"
    assert manifest["packets"][0]["article_packet"] == "basics/determined/article.lean"
    assert manifest["packets"][0]["packet_hash"] == report.nodes[0].declarations[0].evidence_hash
    assert manifest["packets"][0]["article_packet_hash"] == report.nodes[0].evidence_hash
    assert manifest["packets"][0]["review_hash"] == report.nodes[0].review_hash
    passage_entry = json.loads((passages / PACKET_MANIFEST).read_text(encoding="utf-8"))[
        "passages"
    ][0]
    passage_bytes = (passages / passage_entry["passage"]).read_bytes()
    assert passage_entry["hash"] == "sha256:" + hashlib.sha256(passage_bytes).hexdigest()
    # The passage never enters the blind packet.
    packet_path = packets / manifest["packets"][0]["packet"]
    assert "line 5" not in packet_path.read_text(encoding="utf-8")
    assert load_skeleton_report_roundtrip(report, tmp_path)


def test_packet_publication_refuses_an_incomplete_report(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    incomplete = replace(report, unresolved=("missing declaration",))
    packets = tmp_path / "packets"

    with pytest.raises(SkeletonError, match="incomplete skeleton report"):
        write_packets(incomplete, packets)

    assert not packets.exists()


def test_cli_does_not_publish_packets_for_unresolved_declarations(
    tmp_path: Path, capsys, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(
        tmp_path,
        lean={"determined": "Skel.observation_determined", "missing": "Skel.absent"},
    )
    monkeypatch.setattr("autoform_cli.skeleton.run_probe", lambda probe, root: _fake_probe_output())
    packets = tmp_path / "packets"
    report_path = tmp_path / "skeleton.json"

    result = main(
        [
            "skeleton",
            str(blueprint),
            "--lean-root",
            str(project),
            "--output",
            str(report_path),
            "--packets",
            str(packets),
        ]
    )

    assert result == 1
    assert not packets.exists()
    assert load_skeleton_report(report_path).unresolved
    assert "refusing to publish review packets" in capsys.readouterr().err


def test_packet_publication_replaces_stale_managed_output(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"

    write_packets(report, packets, passages=passages)
    stale_packet = packets / "stale.lean"
    stale_passage = passages / "stale.txt"
    stale_packet.write_text("stale\n", encoding="utf-8")
    stale_passage.write_text("stale\n", encoding="utf-8")

    write_packets(report, packets, passages=passages)

    assert not stale_packet.exists()
    assert not stale_passage.exists()
    assert json.loads((passages / PACKET_MANIFEST).read_text(encoding="utf-8"))["kind"] == "passages"


def test_packet_publication_refuses_unmanaged_or_symlink_output(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    unmanaged = tmp_path / "unmanaged"
    unmanaged.mkdir()
    (unmanaged / "keep.txt").write_text("mine\n", encoding="utf-8")

    with pytest.raises(SkeletonError, match="non-Autoform packet output"):
        write_packets(report, unmanaged)

    outside = tmp_path / "outside"
    outside.mkdir()
    linked = tmp_path / "linked"
    linked.symlink_to(outside, target_is_directory=True)
    with pytest.raises(SkeletonError, match="symlink packet output"):
        write_packets(report, linked)

    fake_managed = tmp_path / "fake-managed"
    fake_managed.mkdir()
    (fake_managed / PACKET_MANIFEST).write_text(
        SkeletonReport(nodes=(), unresolved=()).to_json(), encoding="utf-8"
    )
    valuable = fake_managed / "valuable.txt"
    valuable.write_text("keep me\n", encoding="utf-8")
    with pytest.raises(SkeletonError, match="non-Autoform packet output"):
        write_packets(report, fake_managed)
    assert valuable.read_text(encoding="utf-8") == "keep me\n"


def test_packet_filenames_cannot_collide_by_case_or_with_article_packet(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    node = report.nodes[0]
    declaration = node.declarations[0]
    report = replace(
        report,
        nodes=(
            replace(
                node,
                declarations=(
                    replace(declaration, name="Foo.x"),
                    replace(declaration, name="foo.x"),
                    replace(declaration, name="article"),
                ),
            ),
        ),
    )

    packets = tmp_path / "packets"
    write_packets(report, packets)
    manifest = json.loads((packets / PACKET_MANIFEST).read_text(encoding="utf-8"))
    relative_paths = [entry["packet"] for entry in manifest["packets"]]

    assert len({path.casefold() for path in relative_paths}) == 3
    assert all((packets / path).is_file() for path in relative_paths)
    assert (packets / "basics" / "determined" / "article.lean").is_file()


def test_packet_publication_rolls_back_both_trees_on_commit_failure(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    (passages / "old-marker").write_text("old passages\n", encoding="utf-8")

    install_output = _install_output

    def fail_passage_install(source: str | Path, destination: str | Path) -> None:
        source_path = Path(source)
        if "autoform-stage" in source_path.name and Path(destination) == passages:
            raise OSError("simulated passage commit failure")
        install_output(source_path, Path(destination))

    monkeypatch.setattr("autoform_cli.skeleton._install_output", fail_passage_install)

    with pytest.raises(SkeletonError, match="could not publish skeleton output"):
        write_packets(report, packets, passages=passages)

    assert (packets / "old-marker").read_text(encoding="utf-8") == "old packets\n"
    assert (passages / "old-marker").read_text(encoding="utf-8") == "old passages\n"


def test_packet_publication_rolls_back_both_trees_when_interrupted(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    (passages / "old-marker").write_text("old passages\n", encoding="utf-8")
    install_output = _install_output

    def interrupt_passage_install(source: str | Path, destination: str | Path) -> None:
        source_path = Path(source)
        install_output(source_path, Path(destination))
        if "autoform-stage" in source_path.name and Path(destination) == passages:
            raise KeyboardInterrupt

    monkeypatch.setattr("autoform_cli.skeleton._install_output", interrupt_passage_install)

    with pytest.raises(KeyboardInterrupt):
        write_packets(report, packets, passages=passages)

    assert (packets / "old-marker").read_text(encoding="utf-8") == "old packets\n"
    assert (passages / "old-marker").read_text(encoding="utf-8") == "old passages\n"


def test_packet_publication_rolls_back_when_interrupted_after_backup_rename(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    packets = tmp_path / "packets"
    write_packets(report, packets)
    marker = packets / "old-marker"
    marker.write_text("old packets\n", encoding="utf-8")
    replace_path = os.replace

    def interrupt_after_backup(source: str | Path, destination: str | Path) -> None:
        replace_path(source, destination)
        if Path(source) == packets and "autoform-backup" in Path(destination).name:
            raise KeyboardInterrupt

    monkeypatch.setattr("autoform_cli.skeleton.os.replace", interrupt_after_backup)

    with pytest.raises(KeyboardInterrupt):
        write_packets(report, packets)

    assert marker.read_text(encoding="utf-8") == "old packets\n"
    assert list(tmp_path.glob(".packets.autoform-backup-*")) == []


def test_packet_publication_preserves_a_changed_backup_during_cleanup(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(
        blueprint,
        lean_root=project,
        runner=lambda probe, root: _fake_probe_output(),
    )
    packets = tmp_path / "packets"
    write_packets(report, packets)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    install_output = _install_output
    changed_backup: Path | None = None

    def change_backup_after_install(source: str | Path, destination: str | Path) -> None:
        nonlocal changed_backup
        install_output(Path(source), Path(destination))
        if "autoform-stage" in Path(source).name and Path(destination) == packets:
            (changed_backup,) = tmp_path.glob(".packets.autoform-backup-*")
            (changed_backup / "concurrent-marker").write_text("keep me\n", encoding="utf-8")

    monkeypatch.setattr("autoform_cli.skeleton._install_output", change_backup_after_install)

    with pytest.warns(RuntimeWarning, match="backup changed.*preserved"):
        write_packets(report, packets)

    assert changed_backup is not None
    assert (changed_backup / "concurrent-marker").read_text(encoding="utf-8") == "keep me\n"
    assert not (packets / "old-marker").exists()


def test_packet_publication_does_not_delete_a_concurrent_replacement(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    replace = os.replace
    install_output = _install_output

    def replace_then_fail(source: str | Path, destination: str | Path) -> None:
        source_path = Path(source)
        destination_path = Path(destination)
        if "autoform-stage" in source_path.name and destination_path == passages:
            displaced = tmp_path / "displaced-packets"
            replace(packets, displaced)
            packets.mkdir()
            (packets / "valuable").write_text("concurrent publisher\n", encoding="utf-8")
            raise OSError("simulated passage commit failure")
        install_output(source_path, destination_path)

    monkeypatch.setattr("autoform_cli.skeleton._install_output", replace_then_fail)

    with pytest.raises(SkeletonError, match="preserved"):
        write_packets(report, packets, passages=passages)

    assert (packets / "valuable").read_text(encoding="utf-8") == "concurrent publisher\n"
    backups = list(tmp_path.glob(".packets.autoform-backup-*"))
    assert len(backups) == 1
    assert (backups[0] / "old-marker").read_text(encoding="utf-8") == "old packets\n"


def test_packet_publication_does_not_replace_a_concurrent_empty_directory(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    write_packets(report, packets)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    install_output = _install_output
    concurrent_inode: int | None = None

    def create_before_install(stage: Path, destination: Path) -> None:
        nonlocal concurrent_inode
        if destination == packets:
            destination.mkdir()
            concurrent_inode = destination.stat().st_ino
        install_output(stage, destination)

    monkeypatch.setattr("autoform_cli.skeleton._install_output", create_before_install)

    with pytest.raises(SkeletonError, match="published output changed during rollback"):
        write_packets(report, packets)

    assert concurrent_inode is not None
    assert packets.stat().st_ino == concurrent_inode
    assert list(packets.iterdir()) == []
    backups = list(tmp_path.glob(".packets.autoform-backup-*"))
    assert len(backups) == 1
    assert (backups[0] / "old-marker").read_text(encoding="utf-8") == "old packets\n"


def test_packet_publication_preflights_no_replace_before_moving_old_tree(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    write_packets(report, packets)
    marker = packets / "old-marker"
    marker.write_text("old packets\n", encoding="utf-8")

    def unavailable(source: Path, destination: Path) -> None:
        raise SkeletonError(["atomic no-replace rename is unavailable"])

    monkeypatch.setattr("autoform_cli.skeleton._rename_no_replace", unavailable)

    with pytest.raises(SkeletonError, match="no-replace rename is unavailable"):
        write_packets(report, packets)

    assert marker.read_text(encoding="utf-8") == "old packets\n"
    assert list(tmp_path.glob(".packets.autoform-backup-*")) == []
    assert list(tmp_path.glob(".packets.autoform-preflight-*")) == []


def test_packet_publication_cleans_up_an_interrupted_preflight(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    write_packets(report, packets)
    marker = packets / "old-marker"
    marker.write_text("old packets\n", encoding="utf-8")
    install_output = _install_output

    def interrupt_after_preflight_install(stage: Path, destination: Path) -> None:
        install_output(stage, destination)
        if "autoform-preflight" in destination.parent.name:
            raise KeyboardInterrupt

    monkeypatch.setattr(
        "autoform_cli.skeleton._install_output", interrupt_after_preflight_install
    )

    with pytest.raises(KeyboardInterrupt):
        write_packets(report, packets)

    assert marker.read_text(encoding="utf-8") == "old packets\n"
    assert list(tmp_path.glob(".packets.autoform-backup-*")) == []
    assert list(tmp_path.glob(".packets.autoform-preflight-*")) == []


def test_packet_publication_restores_old_trees_when_quarantine_cleanup_fails(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    (passages / "old-marker").write_text("old passages\n", encoding="utf-8")
    install_output = _install_output
    remove_output = _remove_output

    def fail_passage_install(stage: Path, destination: Path) -> None:
        if "autoform-stage" in stage.name and destination == passages:
            raise OSError("simulated passage install failure")
        install_output(stage, destination)

    def fail_quarantine_cleanup(path: Path) -> None:
        if "autoform-rollback" in path.name:
            raise OSError("simulated quarantine cleanup failure")
        remove_output(path)

    monkeypatch.setattr("autoform_cli.skeleton._install_output", fail_passage_install)
    monkeypatch.setattr("autoform_cli.skeleton._remove_output", fail_quarantine_cleanup)

    with pytest.raises(SkeletonError, match="preserved for recovery"):
        write_packets(report, packets, passages=passages)

    assert (packets / "old-marker").read_text(encoding="utf-8") == "old packets\n"
    assert (passages / "old-marker").read_text(encoding="utf-8") == "old passages\n"
    quarantines = list(tmp_path.glob(".packets.autoform-rollback-*"))
    assert len(quarantines) == 1
    assert (quarantines[0] / PACKET_MANIFEST).is_file()


def test_packet_publication_does_not_overwrite_during_backup_restore(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    write_packets(report, packets, passages=passages)
    (packets / "old-marker").write_text("old packets\n", encoding="utf-8")
    (passages / "old-marker").write_text("old passages\n", encoding="utf-8")
    install_output = _install_output
    rename_no_replace = _rename_no_replace
    concurrent_inode: int | None = None

    def fail_passage_install(stage: Path, destination: Path) -> None:
        if "autoform-stage" in stage.name and destination == passages:
            raise OSError("simulated passage install failure")
        install_output(stage, destination)

    def create_before_restore(source: Path, destination: Path) -> None:
        nonlocal concurrent_inode
        if destination == packets and "autoform-backup" in source.name:
            destination.mkdir()
            concurrent_inode = destination.stat().st_ino
        rename_no_replace(source, destination)

    monkeypatch.setattr("autoform_cli.skeleton._install_output", fail_passage_install)
    monkeypatch.setattr("autoform_cli.skeleton._rename_no_replace", create_before_restore)

    with pytest.raises(SkeletonError, match="could not restore skeleton output"):
        write_packets(report, packets, passages=passages)

    assert concurrent_inode is not None
    assert packets.stat().st_ino == concurrent_inode
    assert list(packets.iterdir()) == []
    assert (passages / "old-marker").read_text(encoding="utf-8") == "old passages\n"
    backups = list(tmp_path.glob(".packets.autoform-backup-*"))
    assert len(backups) == 1
    assert (backups[0] / "old-marker").read_text(encoding="utf-8") == "old packets\n"


def test_packet_publication_uses_normal_modes_and_preserves_existing_mode(tmp_path: Path) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    control = tmp_path / "control"
    control.mkdir()

    write_packets(report, packets)

    assert stat.S_IMODE(packets.stat().st_mode) == stat.S_IMODE(control.stat().st_mode)
    packets.chmod(0o750)
    write_packets(report, packets)
    assert stat.S_IMODE(packets.stat().st_mode) == 0o750


def test_packet_publication_cleans_up_when_second_stage_fails(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    passages = tmp_path / "passages"
    stage_output = _stage_output
    calls = 0

    def fail_second_stage(destination: Path) -> Path:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("simulated passage staging failure")
        return stage_output(destination)

    monkeypatch.setattr("autoform_cli.skeleton._stage_output", fail_second_stage)

    with pytest.raises(SkeletonError, match="could not prepare skeleton output"):
        write_packets(report, packets, passages=passages)

    assert list(tmp_path.glob(".packets.autoform-stage-*")) == []
    assert not packets.exists() and not passages.exists()


def test_packet_publication_detects_a_concurrent_file_edit(tmp_path: Path, monkeypatch) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    write_packets(report, packets)
    marker = packets / "review.txt"
    marker.write_text("before\n", encoding="utf-8")

    def edit_then_replace(outputs) -> None:
        marker.write_text("concurrent edit\n", encoding="utf-8")
        _replace_outputs(outputs)

    monkeypatch.setattr("autoform_cli.skeleton._replace_outputs", edit_then_replace)

    with pytest.raises(SkeletonError, match="changed during publication"):
        write_packets(report, packets)
    assert marker.read_text(encoding="utf-8") == "concurrent edit\n"


def test_packet_publication_checks_the_isolated_old_tree_before_install(
    tmp_path: Path, monkeypatch
) -> None:
    project = _project(tmp_path)
    blueprint = _blueprint(tmp_path, lean={"determined": "Skel.observation_determined"})
    report = extract_skeletons(blueprint, lean_root=project, runner=lambda p, r: _fake_probe_output())
    packets = tmp_path / "packets"
    write_packets(report, packets)
    marker = packets / "review.txt"
    marker.write_text("before\n", encoding="utf-8")
    replace = os.replace

    def edit_before_backup(source: str | Path, destination: str | Path) -> None:
        if Path(source) == packets and "autoform-backup" in Path(destination).name:
            marker.write_text("concurrent edit\n", encoding="utf-8")
        replace(source, destination)

    monkeypatch.setattr("autoform_cli.skeleton.os.replace", edit_before_backup)

    with pytest.raises(SkeletonError, match="changed during publication"):
        write_packets(report, packets)
    assert marker.read_text(encoding="utf-8") == "concurrent edit\n"


def load_skeleton_report_roundtrip(report, tmp_path: Path) -> bool:
    path = tmp_path / "r.json"
    path.write_text(report.to_json(), encoding="utf-8")
    return load_skeleton_report(path) == report
