from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_cli.__main__ import main
from autoform_cli.readback import load_readbacks
from autoform_cli.review import REVIEW_PACKET_SCHEMA, load_review_bundle
from autoform_cli.skeleton import DeclarationSkeleton, NodeSkeleton, SkeletonReport


def _blueprint(root: Path) -> Path:
    blueprint = root / "blueprint"
    chapter = blueprint / "roadmap" / "basics"
    chapter.mkdir(parents=True)
    (blueprint / "README.md").write_text("# Blueprint\n", encoding="utf-8")
    (blueprint / "roadmap" / "README.md").write_text(
        "# Roadmap\n\n- [Basics](basics/README.md)\n",
        encoding="utf-8",
    )
    (chapter / "README.md").write_text(
        "# Basics\n\n- [Result](result.md)\n",
        encoding="utf-8",
    )
    (chapter / "result.md").write_text(
        "---\n"
        "article_id: af_0123456789abcdef01234567\n"
        "declaration: theorem\n"
        "lean: Review.result\n"
        "statement: formalized\n"
        "---\n\n"
        "# Result\n\nEvery object is equal to itself.\n\n"
        "## Depends on\n\nNone.\n",
        encoding="utf-8",
    )
    coverage = blueprint / "coverage" / "README.md"
    coverage.parent.mkdir()
    coverage.write_text(
        "# Coverage\n\n"
        "| Area | Coverage | Evidence |\n"
        "| --- | --- | --- |\n"
        "| Scope | OUT | Test fixture |\n",
        encoding="utf-8",
    )
    return blueprint


def _skeleton() -> SkeletonReport:
    declaration = DeclarationSkeleton(
        name="Review.result",
        kind="theorem",
        module="Review",
        path="Review.lean",
        start_line=1,
        end_line=1,
        signature="Review.result : True",
        semantic='{"const":"True"}',
        lean_version="4.32.2",
        depends=(),
        trusted=(),
        assumed=(),
        assumed_semantics=(),
        boundary_modules=(),
        axioms=(),
        axiom_semantics=(),
    )
    return SkeletonReport(
        nodes=(
            NodeSkeleton(
                node_id="basics/result",
                article_path="roadmap/basics/result.md",
                declarations=(declaration,),
            ),
        ),
        unresolved=(),
    )


def test_review_cli_prepares_records_and_checks_exact_evidence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    blueprint = _blueprint(tmp_path)
    skeleton = _skeleton()
    extraction_scopes: list[object] = []

    def extract(*args: object, **kwargs: object) -> SkeletonReport:
        extraction_scopes.append(kwargs.get("node_ids"))
        return skeleton

    monkeypatch.setattr("autoform_cli.__main__.extract_skeletons", extract)
    bundle_path = tmp_path / "review.json"
    packets = tmp_path / "packets"

    assert main(
        [
            "review",
            "prepare",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--output",
            str(bundle_path),
            "--packets",
            str(packets),
        ]
    ) == 0
    capsys.readouterr()
    bundle = load_review_bundle(bundle_path)
    manifest = json.loads((packets / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["schema"] == REVIEW_PACKET_SCHEMA
    packet = packets / manifest["packets"][0]["packet"]
    assert packet.parent.name == "blind"
    assert packet.name == skeleton.nodes[0].declarations[0].evidence_hash.removeprefix("sha256:") + ".lean"
    assert "Review.result" not in packet.as_posix() and "basics" not in packet.as_posix()
    testimony = tmp_path / "testimony.md"
    testimony.write_text("For the unique proposition, the proposition is true.\n", encoding="utf-8")

    assert main(
        [
            "review",
            "record",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--bundle",
            str(bundle_path),
            "--article-id",
            "af_0123456789abcdef01234567",
            "--declaration",
            "Review.result",
            "--packet",
            str(packet),
            "--testimony",
            str(testimony),
            "--model",
            "test-model",
        ]
    ) == 0
    capsys.readouterr()
    assert extraction_scopes == [None, ("basics/result",)]
    cards = load_readbacks(blueprint)
    assert cards[("af_0123456789abcdef01234567", "Review.result")].shown_text == packet.read_text(
        encoding="utf-8"
    )

    assert main(
        [
            "review",
            "check",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--bundle",
            str(bundle_path),
        ]
    ) == 1
    output = capsys.readouterr().out
    assert "review-unapproved" in output

    approval = bundle.review_hash("af_0123456789abcdef01234567", cards)
    article = blueprint / "roadmap/basics/result.md"
    article.write_text(
        article.read_text(encoding="utf-8").replace(
            "statement: formalized\n",
            f"statement: formalized\nreview_approved: {approval}\n",
        ),
        encoding="utf-8",
    )
    assert main(
        [
            "review",
            "check",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--bundle",
            str(bundle_path),
        ]
    ) == 0
    assert "OK: statement reviews match" in capsys.readouterr().out


def test_review_record_rejects_packet_bytes_that_differ_from_bundle(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    blueprint = _blueprint(tmp_path)
    skeleton = _skeleton()
    monkeypatch.setattr("autoform_cli.__main__.extract_skeletons", lambda *args, **kwargs: skeleton)
    bundle_path = tmp_path / "review.json"
    packets = tmp_path / "packets"
    assert main(
        [
            "review",
            "prepare",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--output",
            str(bundle_path),
            "--packets",
            str(packets),
        ]
    ) == 0
    capsys.readouterr()
    packet = tmp_path / "changed.lean"
    packet.write_bytes(skeleton.nodes[0].declarations[0].blind_text().encode("utf-8") + b"\n")
    testimony = tmp_path / "testimony.md"
    testimony.write_text("A testimony.\n", encoding="utf-8")

    assert main(
        [
            "review",
            "record",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--bundle",
            str(bundle_path),
            "--article-id",
            "af_0123456789abcdef01234567",
            "--declaration",
            "Review.result",
            "--packet",
            str(packet),
            "--testimony",
            str(testimony),
            "--model",
            "test-model",
        ]
    ) == 2
    assert "packet bytes do not match" in capsys.readouterr().err


def test_review_prepare_reports_output_filesystem_errors(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    blueprint = _blueprint(tmp_path)
    monkeypatch.setattr("autoform_cli.__main__.extract_skeletons", lambda *args, **kwargs: _skeleton())
    output = tmp_path / "review.json"
    output.mkdir()

    assert main(
        [
            "review",
            "prepare",
            str(blueprint),
            "--lean-root",
            str(tmp_path),
            "--output",
            str(output),
        ]
    ) == 2
    assert "error:" in capsys.readouterr().err
