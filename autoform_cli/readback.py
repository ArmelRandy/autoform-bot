"""Read-backs: blind testimony about what a skeleton literally asserts.

A skeleton tells a reviewer what to read. A read-back tells them what it says,
in mathematical English, written by someone who was shown only the Lean and
never the article, the source, or the author's intent. The reviewer then
compares the read-back with the source statement; every gap between the two is
exactly what they are looking for. The practice follows the read-back audits
of the Prove2me platform.

Read-backs live in the vault under ``blueprint/readbacks/<article id>/<Lean
name>.md``. Each file is a self-contained review card: the exact skeleton the
auditor was shown, in a Lean block, followed by the testimony under a
``## Read-back`` heading, so a reviewer working in the vault sees the Lean and
its rendering side by side without the site. They are testimony, not derived
state, so they are committed with the book, and each one records the skeleton
hash it testifies about and the evidence hash of the packet text it was
written from. When the skeleton's meaning moves, the read-back is stale; when
only the packet text changes, it is revised; the audit says so either way,
and the renderer still shows it, marked as testimony about an earlier
skeleton, rather than silently presenting stale evidence as current.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass
from pathlib import Path

from .markdown import frontmatter_end
from .skeleton import DeclarationSkeleton, SkeletonReport, evidence_hash_of

READBACKS_DIR = "readbacks"
READBACK_HEADING = "## Read-back"
SKELETON_HEADING = "## Skeleton"
#: The only hash form a card may record: what `autoform skeleton` prints.
_HASH = re.compile(r"sha256:[0-9a-f]{64}\Z")
#: The packet a card displays, between the skeleton heading and its fence.
_SHOWN = re.compile(
    r"^" + re.escape(SKELETON_HEADING) + r"\s*\n+```lean\n(?P<packet>.*?)\n```",
    re.MULTILINE | re.DOTALL,
)


@dataclass(frozen=True, slots=True)
class Readback:
    """One read-back file, parsed."""

    node_id: str
    declaration: str
    skeleton_hash: str | None
    #: The evidence hash of the packet the auditor read, if the card records it.
    packet_hash: str | None
    model: str | None
    #: The testimony alone, without the skeleton block the file also carries.
    text: str
    path: Path
    #: The evidence hash of the packet the card *shows*, which a reviewer reads
    #: beside the testimony. ``None`` when the card displays no packet.
    shown_hash: str | None = None

    @property
    def shows_what_it_attests(self) -> bool:
        """Whether the displayed packet is the one the card's hash names.

        A card is read in the vault, so the Lean a reviewer sees is the
        evidence. An edit to that block would otherwise leave the hashes
        attesting to a packet nobody read.
        """

        return self.shown_hash is None or self.shown_hash == self.packet_hash

    def status(self, skeleton: DeclarationSkeleton) -> str:
        """``current``, ``revised`` (same meaning, packet text changed), or ``stale``."""

        if self.skeleton_hash != skeleton.hash:
            return "stale"
        if self.packet_hash is not None and self.packet_hash != skeleton.evidence_hash:
            return "revised"
        return "current"


def readback_path(blueprint: Path, node_id: str, declaration: str) -> Path:
    """The card's place in the vault; refuses names that would leave the readbacks tree."""

    parts = node_id.split("/")
    if not node_id or any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"invalid article id for a read-back: {node_id!r}")
    if not declaration or "/" in declaration or "\\" in declaration or declaration in {".", ".."}:
        raise ValueError(f"invalid declaration name for a read-back: {declaration!r}")
    return blueprint / READBACKS_DIR / Path(*parts) / f"{declaration}.md"


def load_readbacks(blueprint: str | Path) -> dict[tuple[str, str], Readback]:
    """Read every read-back in the vault, keyed by article id and Lean name."""

    root = Path(blueprint).expanduser().resolve() / READBACKS_DIR
    found: dict[tuple[str, str], Readback] = {}
    if not root.is_dir():
        return found
    for path in sorted(root.rglob("*.md")):
        # A card is a file inside the vault; a symlink could point anywhere.
        if path.is_symlink() or not path.is_file():
            continue
        if any((root / parent).is_symlink() for parent in path.relative_to(root).parents):
            continue
        relative = path.relative_to(root)
        node_id = relative.parent.as_posix()
        declaration = relative.stem
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        metadata, body = _split(text)
        shown = _SHOWN.search(body)
        found[(node_id, declaration)] = Readback(
            node_id=node_id,
            declaration=metadata.get("declaration") or declaration,
            skeleton_hash=_hash_or_none(metadata.get("skeleton")),
            packet_hash=_hash_or_none(metadata.get("packet")),
            model=metadata.get("model"),
            text=_testimony(body),
            path=path,
            shown_hash=evidence_hash_of(shown.group("packet") + "\n") if shown else None,
        )
    return found


def write_readback(
    blueprint: str | Path,
    *,
    node_id: str,
    declaration: DeclarationSkeleton,
    model: str,
    text: str,
) -> Path:
    """File a read-back for ``declaration`` under the article it belongs to."""

    path = readback_path(Path(blueprint).expanduser().resolve(), node_id, declaration.name)
    if path.is_symlink():
        raise ValueError(f"refusing to write a read-back through a symlink: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    content = "\n".join(
        [
            "---",
            f"declaration: {declaration.name}",
            f"skeleton: {declaration.hash}",
            f"packet: {declaration.evidence_hash}",
            f"model: {model}",
            "---",
            "",
            f"# {declaration.name}",
            "",
            f"Article `{node_id}` · {declaration.kind} · skeleton `{declaration.hash[:12]}…` · read back by {model}.",
            "",
            "## Skeleton",
            "",
            "```lean",
            declaration.blind_text().rstrip("\n"),
            "```",
            "",
            READBACK_HEADING,
            "",
            text.strip("\n"),
            "",
        ]
    )
    # Write whole or not at all: a reviewer never sees a half-written card.
    staged = path.with_name(path.name + ".tmp")
    staged.write_text(content, encoding="utf-8")
    os.replace(staged, path)
    return path


@dataclass(frozen=True, slots=True)
class ReadbackFinding:
    """A read-back that is missing or no longer testifies about the current skeleton."""

    node_id: str
    declaration: str
    code: str
    reason: str


def readback_findings(
    report: SkeletonReport,
    readbacks: dict[tuple[str, str], Readback],
) -> list[ReadbackFinding]:
    """Compare every skeleton with the testimony filed for it."""

    findings: list[ReadbackFinding] = []
    for node in report.nodes:
        for declaration in node.declarations:
            readback = readbacks.get((node.node_id, declaration.name))
            if readback is None:
                findings.append(
                    ReadbackFinding(
                        node.node_id,
                        declaration.name,
                        "readback-missing",
                        f"no read-back filed for {declaration.name}; write one from its blind packet",
                    )
                )
            elif readback.status(declaration) == "stale":
                findings.append(
                    ReadbackFinding(
                        node.node_id,
                        declaration.name,
                        "readback-stale",
                        (
                            f"read-back for {declaration.name} testifies about skeleton "
                            f"{readback.skeleton_hash}; the current skeleton is {declaration.hash}"
                            if readback.skeleton_hash
                            else f"read-back for {declaration.name} records no valid skeleton hash; "
                            f"the current skeleton is {declaration.hash}"
                        ),
                    )
                )
            elif not readback.shows_what_it_attests:
                findings.append(
                    ReadbackFinding(
                        node.node_id,
                        declaration.name,
                        "readback-altered",
                        f"read-back for {declaration.name} shows a packet that is not the one it "
                        f"records ({readback.packet_hash}); the card was edited after it was filed",
                    )
                )
            elif readback.status(declaration) == "revised":
                findings.append(
                    ReadbackFinding(
                        node.node_id,
                        declaration.name,
                        "readback-revised",
                        f"read-back for {declaration.name} was written from packet "
                        f"{readback.packet_hash}; the packet text is now {declaration.evidence_hash}",
                    )
                )
    # Testimony about a declaration the blueprint no longer names is evidence
    # for nothing, and would otherwise sit in the vault unmentioned forever.
    named = {(node.node_id, declaration.name) for node in report.nodes for declaration in node.declarations}
    for node_id, name in sorted(set(readbacks) - named):
        findings.append(
            ReadbackFinding(
                node_id,
                name,
                "readback-orphaned",
                f"read-back filed for {name} under {node_id}, which names no such declaration; "
                "the statement was renamed or removed, so delete the card or restore the name",
            )
        )
    return findings


def _hash_or_none(value: str | None) -> str | None:
    """A recorded hash, or ``None`` when the card carries none or a malformed one."""

    return value if value is not None and _HASH.fullmatch(value) else None


def _testimony(body: str) -> str:
    """Return the text under ``## Read-back``, or the whole body of an older file."""

    lines = body.splitlines()
    for index, line in enumerate(lines):
        if line.strip().casefold() == READBACK_HEADING.casefold():
            return "\n".join(lines[index + 1 :]).strip("\n")
    return body.strip("\n")


def _split(text: str) -> tuple[dict[str, str], str]:
    lines = text.splitlines()
    end = frontmatter_end(lines)
    metadata: dict[str, str] = {}
    if end:
        for raw in lines[1 : end - 1]:
            if ":" in raw:
                key, value = (part.strip() for part in raw.split(":", 1))
                if key and value:
                    metadata[key] = value
    return metadata, "\n".join(lines[end:])


__all__ = [
    "READBACKS_DIR",
    "READBACK_HEADING",
    "Readback",
    "ReadbackFinding",
    "load_readbacks",
    "readback_findings",
    "readback_path",
    "write_readback",
]
