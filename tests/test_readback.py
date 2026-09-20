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

_PROP = '{"type":{"sort":{"zero":null}}}'
_BODY = '{"type":{"sort":{"zero":null}},"value":{"bvar":0}}'
_OTHER_BODY = '{"type":{"sort":{"zero":null}},"value":{"bvar":1}}'


# --------------------------------------------------------------------------- #
# Fixtures
# --------------------------------------------------------------------------- #


def _trusted(source: str, semantic: str = _BODY) -> TrustedDeclaration:
    return TrustedDeclaration(
        name="Skel.IsSup",
        kind="def",
        module="Skel.Defs",
        path="Skel/Defs.lean",
        start_line=3,
        end_line=4,
        signature="Skel.IsSup {S : Type} [LinearOrder S] (E : Set S) (b : S) : Prop",
        semantic=semantic,
        depends=(),
        source=source,
    )


def _declaration(
    source: str = "/-- doc -/\ndef IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b",
    semantic: str = _BODY,
) -> DeclarationSkeleton:
    """A theorem resting on one definition; ``semantic`` is the definition's elaborated body."""

    return DeclarationSkeleton(
        name="Skel.sup_unique",
        kind="theorem",
        module="Skel.Main",
        path="Skel/Main.lean",
        start_line=10,
        end_line=14,
        signature="Skel.sup_unique {E : Set ℝ} {a b : ℝ} (ha : Skel.IsSup E a) (hb : Skel.IsSup E b) : a = b",
        semantic=_PROP,
        lean_version="4.32.2",
        depends=("Skel.IsSup",),
        trusted=(_trusted(source, semantic),),
        assumed=(),
        assumed_semantics=(),
        boundary_modules=(),
        axioms=("propext",),
        axiom_semantics=(("propext", _PROP),),
    )


def _report(declaration: DeclarationSkeleton | None = None) -> SkeletonReport:
    declaration = declaration or _declaration()
    node = NodeSkeleton(node_id="basics/sup-unique", article_path="roadmap/basics/sup-unique.md", declarations=(declaration,))
    return SkeletonReport(nodes=(node,), unresolved=())


def _blueprint(root: Path, *, approved: str | None = None, evidence: str | None = None) -> Path:
    blueprint = root / "blueprint"
    chapter = blueprint / "roadmap" / "basics"
    chapter.mkdir(parents=True)
    (blueprint / "roadmap" / "README.md").write_text("# Roadmap\n\n- [Basics](basics/README.md)\n", encoding="utf-8")
    (chapter / "README.md").write_text("# Basics\n\nOne result.\n\n- [Sup unique](sup-unique.md)\n", encoding="utf-8")
    frontmatter = ["---", "declaration: theorem", "lean: Skel.sup_unique", "statement: formalized"]
    if approved:
        frontmatter.append(f"skeleton_approved: {approved}")
    if evidence:
        frontmatter.append(f"skeleton_evidence: {evidence}")
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


def test_the_semantic_hash_ignores_presentation_and_the_evidence_hash_does_not() -> None:
    base = _declaration()
    reworded = _declaration("/-- a clearer docstring -/\ndef IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b  -- note")
    respaced = _declaration("def IsSup (E : Set S) (b : S) : Prop :=\n  ∀ x ∈ E, x ≤ b")
    changed = _declaration("def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x < b", semantic=_OTHER_BODY)

    assert base.hash.startswith("sha256:") and len(base.hash) == 71
    # meaning: unchanged by comments and layout, changed by the elaborated body
    assert base.hash == reworded.hash == respaced.hash != changed.hash
    # evidence: the exact packet text, so a comment leaves it alone but layout does not
    assert base.evidence_hash == reworded.evidence_hash != respaced.evidence_hash
    # a one-declaration article shares its declaration's meaning hash; its evidence hash covers the joint packet
    assert _report().nodes[0].hash == base.hash and _report().nodes[0].evidence_hash != base.evidence_hash


def test_a_multi_declaration_article_hashes_all_of_them() -> None:
    first = _declaration()
    second = DeclarationSkeleton(**{**{name: getattr(first, name) for name in first.__slots__}, "name": "Skel.other"})
    node = NodeSkeleton(node_id="basics/pair", article_path="roadmap/basics/pair.md", declarations=(first, second))

    assert node.hash not in {first.hash, second.hash}
    assert node.evidence_hash not in {first.evidence_hash, second.evidence_hash}


def test_blind_packets_strip_every_comment_and_name_nothing_else(tmp_path: Path) -> None:
    report = _report()

    written = write_packets(report, tmp_path / "packets")

    manifest = json.loads((tmp_path / "packets" / PACKET_MANIFEST).read_text(encoding="utf-8"))
    (entry,) = manifest["packets"]
    article = tmp_path / "packets" / entry["article_packet"]
    packet = tmp_path / "packets" / entry["packet"]
    assert set(written) == {article, packet}
    assert article.read_text(encoding="utf-8").startswith("-- article with 1 declaration(s)\n-- theorem Skel.sup_unique")
    text = packet.read_text(encoding="utf-8")
    assert "doc" not in text
    assert "-- signature: Skel.IsSup {S : Type} [LinearOrder S] (E : Set S) (b : S) : Prop" in text
    assert "def IsSup (E : Set S) (b : S) : Prop := ∀ x ∈ E, x ≤ b" in text
    assert "sup-unique" not in text and "roadmap" not in text
    declaration = report.nodes[0].declarations[0]
    assert entry["declaration"] == "Skel.sup_unique" and entry["node_id"] == "basics/sup-unique"
    assert entry["packet"].startswith("basics/sup-unique/Skel.sup_unique")
    # what a read-back records: the meaning it testifies about and the text it was written from
    assert entry["hash"] == declaration.hash and entry["packet_hash"] == declaration.evidence_hash


def test_the_source_and_hashes_round_trip_through_the_report(tmp_path: Path) -> None:
    report = _report()
    path = tmp_path / "skeleton.json"
    path.write_text(report.to_json(), encoding="utf-8")

    loaded = load_skeleton_report(path)

    assert loaded == report
    assert loaded.nodes[0].declarations[0].trusted[0].source == report.nodes[0].declarations[0].trusted[0].source
    node = json.loads(report.to_json())["nodes"][0]
    assert node["hash"] == report.nodes[0].hash and node["evidence_hash"] == report.nodes[0].evidence_hash


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
    assert (readback.model, readback.text) == ("test-model", "Let $E$ …")
    assert (readback.skeleton_hash, readback.packet_hash) == (declaration.hash, declaration.evidence_hash)
    assert readback.status(declaration) == "current"
    # same meaning, different packet text: revised; different meaning: stale
    assert readback.status(_declaration("def IsSup (E : Set S) (b : S) : Prop :=\n  ∀ x ∈ E, x ≤ b")) == "revised"
    assert readback.status(_declaration("def IsSup (E : Set S) (b : S) : Prop := True", semantic=_OTHER_BODY)) == "stale"
    assert readback_findings(_report(declaration), readbacks) == []


def test_missing_stale_and_revised_readbacks_are_reported(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path)
    old = _declaration("def IsSup (E : Set S) (b : S) : Prop := True", semantic=_OTHER_BODY)
    write_readback(blueprint, node_id="basics/sup-unique", declaration=old, model="m", text="Anything.")

    (stale,) = readback_findings(_report(), load_readbacks(blueprint))
    assert (stale.code, stale.declaration) == ("readback-stale", "Skel.sup_unique")
    assert old.hash in stale.reason and _declaration().hash in stale.reason

    respaced = _declaration("def IsSup (E : Set S) (b : S) : Prop :=\n  ∀ x ∈ E, x ≤ b")
    write_readback(blueprint, node_id="basics/sup-unique", declaration=respaced, model="m", text="Anything.")
    (revised,) = readback_findings(_report(), load_readbacks(blueprint))
    assert revised.code == "readback-revised" and _declaration().evidence_hash in revised.reason

    (missing,) = readback_findings(_report(), {})
    assert missing.code == "readback-missing"


# --------------------------------------------------------------------------- #
# Approval in the article, checked by the audit
# --------------------------------------------------------------------------- #


def test_the_article_records_the_approved_hashes(tmp_path: Path) -> None:
    article = _report().nodes[0]
    blueprint = _blueprint(tmp_path, approved=article.hash, evidence=article.evidence_hash)

    node = load_graph(blueprint).nodes["basics/sup-unique"]
    assert (node.skeleton_approved, node.skeleton_evidence) == (article.hash, article.evidence_hash)

    article = blueprint / "roadmap" / "basics" / "sup-unique.md"
    article.write_text(article.read_text(encoding="utf-8").replace(_declaration().hash, "approved"), encoding="utf-8")
    with pytest.raises(GraphValidationError) as caught:
        load_graph(blueprint)
    assert "skeleton_approved" in caught.value.issues[0]


def test_audit_reports_drift_and_readback_state_against_the_skeleton(tmp_path: Path) -> None:
    article = _report().nodes[0]
    blueprint = _blueprint(tmp_path, approved=article.hash, evidence=article.evidence_hash)
    write_readback(blueprint, node_id="basics/sup-unique", declaration=_declaration(), model="m", text="Fine.")

    assert audit_blueprint(blueprint, skeleton=_report()).clean
    assert audit_blueprint(blueprint).clean  # without a report, nothing is checked

    drifted = _report(_declaration("def IsSup (E : Set S) (b : S) : Prop := True", semantic=_OTHER_BODY))
    codes = [(finding.code, finding.article_path) for finding in audit_blueprint(blueprint, skeleton=drifted).findings]
    assert codes == [
        ("readback-stale", "roadmap/basics/sup-unique.md"),
        ("skeleton-drift", "roadmap/basics/sup-unique.md"),
    ]

    # the meaning stands but the packet text read by the person has changed
    respaced = _report(_declaration("def IsSup (E : Set S) (b : S) : Prop :=\n  ∀ x ∈ E, x ≤ b"))
    codes = sorted(finding.code for finding in audit_blueprint(blueprint, skeleton=respaced).findings)
    assert codes == ["readback-revised", "skeleton-evidence-drift"]


# --------------------------------------------------------------------------- #
# The review surface
# --------------------------------------------------------------------------- #


def test_render_shows_skeleton_and_readback_under_the_statement(tmp_path: Path) -> None:
    article = _report().nodes[0]
    blueprint = _blueprint(tmp_path, approved=article.hash, evidence=article.evidence_hash)
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
    stale = "sha256:" + "0" * 64
    blueprint = _blueprint(tmp_path, approved=stale)

    render_site(blueprint, tmp_path / "site-src", skeleton=_report())

    page = (tmp_path / "site-src" / "roadmap" / "basics" / "README.md").read_text(encoding="utf-8")
    assert f"approval {stale} predates the current skeleton" in page
    assert "No read-back filed for this skeleton yet." in page

    render_site(blueprint, tmp_path / "plain")
    assert "bp-review" not in (tmp_path / "plain" / "roadmap" / "basics" / "README.md").read_text(encoding="utf-8")


# --------------------------------------------------------------------------- #
# Cards are vault files and nothing else
# --------------------------------------------------------------------------- #


def test_card_paths_stay_inside_the_readbacks_tree(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path)
    with pytest.raises(ValueError):
        readback_path(blueprint, "../escape", "Skel.sup_unique")
    with pytest.raises(ValueError):
        readback_path(blueprint, "basics/sup-unique", "../Skel.sup_unique")
    with pytest.raises(ValueError):
        readback_path(blueprint, "basics//sup-unique", "Skel.sup_unique")


def test_malformed_hashes_and_symlinked_cards_are_not_testimony(tmp_path: Path) -> None:
    blueprint = _blueprint(tmp_path)
    path = write_readback(blueprint, node_id="basics/sup-unique", declaration=_declaration(), model="m", text="Fine.")
    path.write_text(path.read_text(encoding="utf-8").replace(_declaration().hash, "approved"), encoding="utf-8")

    readback = load_readbacks(blueprint)[("basics/sup-unique", "Skel.sup_unique")]
    assert readback.skeleton_hash is None and readback.status(_declaration()) == "stale"
    (stale,) = readback_findings(_report(), load_readbacks(blueprint))
    assert stale.code == "readback-stale" and "no valid skeleton hash" in stale.reason

    outside = tmp_path / "outside.md"
    outside.write_text(path.read_text(encoding="utf-8"), encoding="utf-8")
    link = blueprint / "readbacks" / "basics" / "sup-unique" / "Skel.other.md"
    link.symlink_to(outside)
    assert ("basics/sup-unique", "Skel.other") not in load_readbacks(blueprint)
    # a stray temporary file is never a half-written card
    assert not path.with_name(path.name + ".tmp").exists()
