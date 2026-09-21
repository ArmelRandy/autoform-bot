# Writing a read-back

A **read-back** is a rendering, in mathematical English, of what a Lean
skeleton *literally asserts*. It is neither a summary nor an explanation, and
it never guesses at what the author meant. A human reviewer will set it beside
the statement the author intended to formalize; every difference between the
two is exactly what they are looking for. This practice follows the blind
read-back audits used by [Prove2me](https://prove2.me).

## You are working blind, and that is the point

You have been given a packet: the comment-stripped skeleton of one
declaration, written by `autoform skeleton --packets`. It holds the elaborated
signature of a theorem or definition and the source of every project
definition the statement rests on, with all comments and docstrings removed.

You have not been given the article, the source text, or any description of
the intent, and you must not look for them. Do not open the blueprint, the
Lean project, or the source directory. Do not search for the theorem's name on
the web. A reader who knows what the code is supposed to say will read that
meaning into it, and the discrepancies the reviewer needs to see disappear.
If the packet is ambiguous, say what is ambiguous rather than resolving it.

## Principles

1. **Translate the code, not an intent.** State what the Lean says. If it says
   less than a textbook theorem would, your read-back says less.
2. **Account for every binder and hypothesis.** Every quantified variable,
   every explicit and implicit argument, every typeclass assumption appears in
   the read-back. Dropping a hypothesis is the worst failure.
3. **Unfold the project's own definitions.** The packet's definitions are
   there to be unfolded: write what `IsSup E b` means in words, do not name it
   as if it were standard. Library notions such as the real numbers may be
   named without unfolding; when a library notion has a convention a reader
   might not expect, such as division by zero being zero, say so.
4. **Surface degenerate and edge cases.** Say what the quantifiers silently
   include: zero, empty sets, one-element types, junk values of total
   functions, and hypotheses that could never hold. A vacuous theorem is the
   classic faithfulness trap; if the hypotheses can be contradictory, say so.
5. **Preserve logical precision.** Keep the exact strength of every
   connective: `≤` against `<`, existence against unique existence, an
   implication against an equivalence, the direction of every inequality.
6. **Write for a mathematician who does not read Lean.** Plain mathematical
   English with standard notation, in Markdown with LaTeX math. Write $P_i$,
   not `P i`. Do not mention Lean syntax, tactics, or universe levels.
7. **No judgment.** Do not say whether the formalization is right, faithful,
   or well designed, and do not defend it. Report; the reviewer decides.

## Format

One self-contained paragraph per declaration, understandable without the
packet. Completeness beats elegance: this is fine print. Introduce every
variable and symbol before using it, put the main assertion in display math,
and use a short list when the statement has several clauses.

## Filing

Write the read-back to the vault at

```text
blueprint/readbacks/<article id>/<Lean name>.md
```

as a review card: frontmatter copying `declaration`, `hash` (as `skeleton`)
and `packet_hash` (as `packet`) from the packet manifest entry you were given
and naming the model that wrote the text, a
title, the packet verbatim in a `lean` block under `## Skeleton`, and the
testimony under `## Read-back`. The `autoform_cli.readback.write_readback`
helper writes this layout; only the text under `## Read-back` is published:

```markdown
---
declaration: RealAnalysis.isInf_one_div_nat
skeleton: sha256:3f9a2c1d…   # the semantic hash, copied in full
packet: sha256:8c4e1b2a…     # the evidence hash of the packet read, in full
model: claude-fable-5-1       # a label, not provenance: nothing verifies it
---

# RealAnalysis.isInf_one_div_nat

## Skeleton

```lean
-- theorem RealAnalysis.isInf_one_div_nat
...
```

## Read-back

Let $S$ be ...
```

A read-back testifies about one skeleton. If the skeleton's meaning changes,
the audit reports the read-back as stale and it must be rewritten from the
new packet; if only the packet text changes, it is reported as revised and
should be re-read against the new packet.
