from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_cli.audit import audit_blueprint
from autoform_cli.graph import GraphValidationError, load_graph
from autoform_cli.readback import load_readbacks, readback_findings, readback_path, write_readback
from autoform_cli.render import render_site
from autoform_cli.skeleton import (
    PACKET_MANIFEST,
    DeclarationSkeleton,
    NodeSkeleton,
    SkeletonReport,
    TrustedDeclaration,
    load_skeleton_report,
    write_packets,
)


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #


def _trusted(source: str) -> TrustedDeclaration:
    return TrustedDeclaration(
        name="Skel.IsSup",
        kind="def",
        module="Skel.Defs",
        path="Skel/Defs.lean",
        start_line=3,
        end_line=4,
        signature="Skel.IsSup {S : Type} [LinearOrder S] (E : Set S) (b : S) : Prop",
        depends=(),
        source=source,
    )


def _declaration(source: str = "/-- doc -/\ndef IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b") -> DeclarationSkeleton:
    return DeclarationSkeleton(
        name="Skel.sup_unique",
        kind="theorem",
        module="Skel.Main",
        path="Skel/Main.lean",
        start_line=10,
        end_line=14,
        signature="Skel.sup_unique {E : Set ℝ} {a b : ℝ} (ha : Skel.IsSup E a) (hb : Skel.IsSup E b) : a = b",
        trusted=(_trusted(source),),
        assumed=("Real",),
        axioms=("propext",),
    )


def _report(declaration: DeclarationSkeleton | None = None) -> SkeletonReport:
    declaration = declaration or _declaration()
    node = NodeSkeleton(node_id="basics/sup-unique", article_path="roadmap/basics/sup-unique.md", declarations=(declaration,))
    return SkeletonReport(nodes=(node,), unresolved=())


def _blueprint(root: Path, *, approved: str | None = None) -> Path:
    blueprint = root / "blueprint"
    chapter = blueprint / "roadmap" / "basics"
    chapter.mkdir(parents=True)
    (blueprint / "roadmap" / "README.md").write_text("# Roadmap\n\n- [Basics](basics/README.md)\n", encoding="utf-8")
    (chapter / "README.md").write_text("# Basics\n\nOne result.\n\n- [Sup unique](sup-unique.md)\n", encoding="utf-8")
    frontmatter = ["---", "declaration: theorem", "lean: Skel.sup_unique", "statement: formalized"]
    if approved:
        frontmatter.append(f"skeleton_approved: {approved}")
    frontmatter.append("---")
    (chapter / "sup-unique.md").write_text(
        "\n".join(frontmatter) + "\n\n# Sup unique\n\nA supremum is unique.\n\n## Depends on\n\nNone.\n",
        encoding="utf-8",
    )
    coverage = blueprint / "coverage"
    coverage.mkdir()
    (coverage / "README.md").write_text(
        "# Coverage\n\n| Area | Coverage | Evidence |\n| --- | --- | --- |\n| All | OUT | scratch |\n",
        encoding="utf-8",
    )
    return blueprint


# --------------------------------------------------------------------------- #
# Hashes and packets
# --------------------------------------------------------------------------- #


def test_a_definition_root_carries_its_body_and_the_hash_covers_it() -> None:
    base = _declaration()
    as_def = DeclarationSkeleton(**{**{name: getattr(base, name) for name in base.__slots__}, "kind": "def"})
    with_body = DeclarationSkeleton(
        **{**{name: getattr(as_def, name) for name in as_def.__slots__}, "source": "/-- d -/\ndef f : ℕ := 1"}
    )
    other_body = DeclarationSkeleton(
        **{**{name: getattr(as_def, name) for name in as_def.__slots__}, "source": "def f : ℕ := 2"}
    )

    assert not base.defines and as_def.defines
    assert with_body.hash != as_def.hash and with_body.hash != other_body.hash
    assert "def f : ℕ := 1" in with_body.blind_text() and "/-- d -/" not in with_body.blind_text()
    assert "def f : ℕ := 1" in with_body.as_dict()["source"]


def test_the_hash_ignores_comments_but_not_meaning() -> None:
    base = _declaration()
    reworded = _declaration("/-- a clearer docstring -/\ndef IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b  -- note")
    changed = _declaration("def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x < b")

    assert len(base.hash) == 16
    assert base.hash == reworded.hash
    assert base.hash != changed.hash
    assert _report().nodes[0].hash == base.hash


def test_a_multi_declaration_article_hashes_all_of_them() -> None:
    first = _declaration()
    second = DeclarationSkeleton(**{**{name: getattr(first, name) for name in first.__slots__}, "name": "Skel.other"})
    node = NodeSkeleton(node_id="basics/pair", article_path="roadmap/basics/pair.md", declarations=(first, second))

    assert node.hash not in {first.hash, second.hash}
    assert len(node.hash) == 16


def test_blind_packets_strip_every_comment_and_name_nothing_else(tmp_path: Path) -> None:
    report = _report()

    written = write_packets(report, tmp_path / "packets")

    article, packet = written
    assert article == tmp_path / "packets" / "basics" / "sup-unique" / "article.lean"
    assert article.read_text(encoding="utf-8").startswith("-- article with 1 declaration(s)\n-- theorem Skel.sup_unique")
    assert packet == tmp_path / "packets" / "basics" / "sup-unique" / "Skel.sup_unique.lean"
    text = packet.read_text(encoding="utf-8")
    assert "doc" not in text
    assert "-- signature: Skel.IsSup {S : Type} [LinearOrder S] (E : Set S) (b : S) : Prop" in text
    assert "def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b" in text
    assert "sup-unique" not in text and "roadmap" not in text
    manifest = json.loads((tmp_path / "packets" / PACKET_MANIFEST).read_text(encoding="utf-8"))
    assert manifest["packets"] == [
        {
            "article_packet": "basics/sup-unique/article.lean",
            "declaration": "Skel.sup_unique",
            "hash": report.nodes[0].declarations[0].hash,
            "node_id": "basics/sup-unique",
            "packet": "basics/sup-unique/Skel.sup_unique.lean",
        }
    ]


def test_the_source_and_hash_round_trip_through_the_report(tmp_path: Path) -> None:
    report = _report()
    path = tmp_path / "skeleton.json"
    path.write_text(report.to_json(), encoding="utf-8")

    loaded = load_skeleton_report(path)

    assert loaded == report
    assert loaded.nodes[0].declarations[0].trusted[0].source == report.nodes[0].declarations[0].trusted[0].source
    assert json.loads(report.to_json())["nodes"][0]["hash"] == report.nodes[0].hash


# --------------------------------------------------------------------------- #
# Read-back files
# --------------------------------------------------------------------------- #


def test_readbacks_are_filed_per_declaration_and_report_their_status(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path)
    declaration = _declaration()

    path = write_readback(blueprint, node_id="basics/sup-unique", declaration=declaration, model="test-model", text="Let $E$ …")

    assert path == readback_path(blueprint, "basics/sup-unique", "Skel.sup_unique")
    # The file is a self-contained review card: title, the skeleton shown to
    # the auditor, then the testimony. Only the testimony is read back.
    card = path.read_text(encoding="utf-8")
    assert "# Skel.sup_unique\n" in card and "## Skeleton\n\n```lean\n" in card and "## Read-back\n\nLet $E$ …" in card
    assert "def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b" in card and "/-- doc -/" not in card
    readbacks = load_readbacks(blueprint)
    readback = readbacks[("basics/sup-unique", "Skel.sup_unique")]
    assert (readback.model, readback.text, readback.skeleton_hash) == ("test-model", "Let $E$ …", declaration.hash)
    assert readback.status(declaration) == "current"
    assert readback.status(_declaration("def IsSup (E : Set S) (b : S) : Prop := True")) == "stale"
    assert readback_findings(_report(declaration), readbacks) == []


def test_missing_and_stale_readbacks_are_reported(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path)
    old = _declaration("def IsSup (E : Set S) (b : S) : Prop := True")
    write_readback(blueprint, node_id="basics/sup-unique", declaration=old, model="m", text="Anything.")

    (stale,) = readback_findings(_report(), load_readbacks(blueprint))
    assert (stale.code, stale.declaration) == ("readback-stale", "Skel.sup_unique")
    assert old.hash in stale.reason and _declaration().hash in stale.reason

    (missing,) = readback_findings(_report(), {})
    assert missing.code == "readback-missing"


# --------------------------------------------------------------------------- #
# Approval in the article, checked by the audit
# --------------------------------------------------------------------------- #


def test_the_article_records_an_approved_hash(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path, approved=_declaration().hash)

    assert load_graph(blueprint).nodes["basics/sup-unique"].skeleton_approved == _declaration().hash

    article = blueprint / "roadmap" / "basics" / "sup-unique.md"
    article.write_text(article.read_text(encoding="utf-8").replace(_declaration().hash, "approved"), encoding="utf-8")
    with pytest.raises(GraphValidationError) as caught:
        load_graph(blueprint)
    assert "skeleton_approved" in caught.value.issues[0]


def test_audit_reports_drift_and_readback_state_against_the_skeleton(tmp_path: Path) -> None:
    approved = _declaration().hash
    blueprint = _blueprint(tmp_path, approved=approved)
    write_readback(blueprint, node_id="basics/sup-unique", declaration=_declaration(), model="m", text="Fine.")

    assert audit_blueprint(blueprint, skeleton=_report()).clean
    assert audit_blueprint(blueprint).clean  # without a report, nothing is checked

    drifted = _report(_declaration("def IsSup (E : Set S) (b : S) : Prop := True"))
    codes = [(finding.code, finding.article_path) for finding in audit_blueprint(blueprint, skeleton=drifted).findings]
    assert codes == [
        ("readback-stale", "roadmap/basics/sup-unique.md"),
        ("skeleton-drift", "roadmap/basics/sup-unique.md"),
    ]


# --------------------------------------------------------------------------- #
# The review surface
# --------------------------------------------------------------------------- #


def test_render_shows_skeleton_and_readback_under_the_statement(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path, approved=_declaration().hash)
    write_readback(blueprint, node_id="basics/sup-unique", declaration=_declaration(), model="m", text="Let $E$ be a set.")

    render_site(blueprint, tmp_path / "site-src", skeleton=_report())

    page = (tmp_path / "site-src" / "roadmap" / "basics" / "README.md").read_text(encoding="utf-8")
    assert '<details class="bp-review" markdown="1">' in page
    assert f"approved · {_declaration().hash}" in page
    assert "-- def Skel.IsSup  (Skel/Defs.lean:3-4)" in page
    assert "def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b" in page
    assert "Let $E$ be a set." in page
    assert "Read-back · m · <span class=\"bp-readback-status\">current</span>" in page
    # Testimony is shown inside the statement, never published as a page.
    assert not (tmp_path / "site-src" / "readbacks").exists()


def test_render_marks_drift_and_missing_readbacks(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path, approved="0123456789abcdef")

    render_site(blueprint, tmp_path / "site-src", skeleton=_report())

    page = (tmp_path / "site-src" / "roadmap" / "basics" / "README.md").read_text(encoding="utf-8")
    assert "approval 0123456789abcdef predates the current skeleton" in page
    assert "No read-back filed for this skeleton yet." in page

    render_site(blueprint, tmp_path / "plain")
    assert "bp-review" not in (tmp_path / "plain" / "roadmap" / "basics" / "README.md").read_text(encoding="utf-8")
