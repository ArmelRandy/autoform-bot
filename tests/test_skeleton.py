from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from autoform_cli.__main__ import main
from autoform_cli.skeleton import (
    PACKET_MANIFEST,
    PROBE_MARKER,
    write_packets,
    SKELETON_SCHEMA,
    SkeletonError,
    extract_skeletons,
    format_report,
    lean_libraries,
    load_skeleton_report,
    module_of,
    parse_probe_output,
    path_of,
    render_probe,
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


def _fake_probe_output() -> str:
    """What the probe says about the fixture, as captured from a real run."""

    eligible = {
        "name": "Skel.Eligible",
        "kind": "def",
        "module": "Skel.Defs",
        "range": [5, 6],
        "signature": "Skel.Eligible {Y : Type} (S : Y → Prop) (y : Y) : Prop",
        "depends": [],
    }
    non_ambiguous = {
        "name": "Skel.NonAmbiguous",
        "kind": "def",
        "module": "Skel.Defs",
        "range": [8, 10],
        "signature": "Skel.NonAmbiguous {Y : Type} (S : Y → Prop) : Prop",
        "depends": ["Skel.Eligible"],
    }
    observation = {
        "name": "Skel.Observation",
        "kind": "structure",
        "module": "Skel.Defs",
        "range": [15, 18],
        "signature": "Skel.Observation (Y : Type) : Type",
        "depends": [],
    }
    return "\n".join(
        [
            "some unrelated line from Lean",
            _record(
                "Skel.observation_determined",
                found=True,
                kind="theorem",
                module="Skel.Main",
                range=[14, 17],
                signature="Skel.observation_determined {Y : Type} (o : Skel.Observation Y) :\n  ∃ y, o.admits y",
                depends=["Skel.NonAmbiguous", "Skel.Observation"],
                # Deliberately out of dependency order: the report must sort them.
                trusted=[non_ambiguous, observation, eligible],
                assumed=["Mathlib.Fake"],
                axioms=["sorryAx"],
            ),
            _record("Skel.ghost", found=False),
        ]
    )


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


def test_probe_refuses_to_render_nothing() -> None:
    with pytest.raises(SkeletonError):
        render_probe(imports=("Skel",), roots=(), project_roots=("Skel",))
    with pytest.raises(SkeletonError):
        render_probe(imports=(), roots=("Skel.x",), project_roots=("Skel",))


def test_parse_probe_output_keys_records_by_root_and_ignores_noise() -> None:
    records = parse_probe_output(_fake_probe_output())

    assert set(records) == {"Skel.observation_determined", "Skel.ghost"}
    assert records["Skel.ghost"] == {"root": "Skel.ghost", "found": False}


def test_parse_probe_output_rejects_malformed_records() -> None:
    with pytest.raises(SkeletonError):
        parse_probe_output(PROBE_MARKER + "{not json")
    with pytest.raises(SkeletonError):
        parse_probe_output(PROBE_MARKER + '{"found": true}')


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

    report = extract_skeletons(blueprint, lean_root=project, runner=lambda probe, root: _fake_probe_output())

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
    write_packets(report, tmp_path / "packets", passages=tmp_path / "passages")
    assert (tmp_path / "passages" / "basics" / "determined" / "passage.txt").read_text(encoding="utf-8") == "line 5\nline 6\nline 7\n"
    manifest = json.loads((tmp_path / "packets" / PACKET_MANIFEST).read_text(encoding="utf-8"))
    assert manifest["packets"][0]["passage"] == "basics/determined/passage.txt"
    assert manifest["packets"][0]["article_packet"] == "basics/determined/article.lean"
    # The passage never enters the blind packet.
    assert "line 5" not in (tmp_path / "packets" / "basics" / "determined" / "Skel.observation_determined.lean").read_text(encoding="utf-8")
    assert load_skeleton_report_roundtrip(report, tmp_path)


def load_skeleton_report_roundtrip(report, tmp_path: Path) -> bool:
    path = tmp_path / "r.json"
    path.write_text(report.to_json(), encoding="utf-8")
    return load_skeleton_report(path) == report
