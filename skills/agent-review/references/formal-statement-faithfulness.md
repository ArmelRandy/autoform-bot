# Formal-statement faithfulness rubric

Judge whether one formal statement, as its skeleton shows it, says what the
source passage says. The source is the reference and is never judged; score
the Lean. Do not score proof quality, code quality, or Mathlib style here.

This rubric differs from [faithfulness](faithfulness.md) in what the judge is
allowed to see. That rubric reviews a finished development with the source and
the Lean side by side. This one reviews a single statement blind: a judge who
knows what the code is meant to say reads that meaning into it, so the intent
is withheld and only the source and the comment-stripped skeleton remain.

## Evidence

You receive exactly two things, and nothing else may be consulted.

1. **The source passage**, verbatim, at the locator the article cites (the
   theorem or definition environment in the vendored source, at its recorded
   lines). If no machine-readable source exists, the article prose is the
   reference instead; say so with `reference: article`, since a paraphrase can
   drift, and lower confidence accordingly.
2. **The blind article packet** written by `autoform skeleton --packets`,
   `article.lean`: for every declaration the article names, its elaborated
   signature, its own source statement when present, the unfolded bodies of
   every project definition it rests on, the library notions it assumes, and
   the axioms it finally uses. Judge the declarations together: a source
   theorem is often an existence half and a uniqueness half, and each alone
   is honestly incomplete. Findings from
   `autoform audit --skeleton` may be attached as facts; they are evidence of
   what the kernel established, never a substitute for the comparison below.
   A packet with no axiom line, as the calibration harness writes them,
   gives no evidence of a proof: `hypothesis-missing: generalizes` and
   `conclusion-stronger: proved` are then unavailable, and the plain
   categories apply.

Do not open the article, the Lean file, the proof, neighbouring declarations,
docstrings, or the web. Names are identifiers, not evidence: `WeilDivisor.Group`
tells you nothing about divisors, and `archimedean_property` tells you nothing
about what is quantified. Read the binders.

## Procedure

Work in three steps and show each.

1. **Card the source.** List its objects with their kinds (a real number, a
   scheme over a field, a smooth manifold), its hypotheses numbered, its
   conclusion, and its quantifier structure. Mark a hypothesis *implicit* when
   the passage uses it without stating it.
2. **Card the formal statement** the same way, after unfolding every project
   definition in the packet. A structure or class the statement quantifies over
   contributes each of its fields as a hypothesis. A library notion contributes
   its convention when the convention changes meaning: division by zero is
   zero, natural subtraction truncates, the supremum of an unbounded set is a
   junk value, a cast may not be injective.
3. **List discrepancies** between the two cards, each with one category from
   the vocabulary below and one line of detail. Then read the score off the
   list. Never adjust it by overall impression.

## Discrepancy vocabulary

| Category | Meaning |
|---|---|
| `object-substituted` | A source object is replaced by a proxy the packet does not connect to it: a ring for a manifold, an arbitrary type for a variety, one symbol for a formula. |
| `hypothesis-missing` | A source hypothesis has no counterpart in the Lean and the conclusion is not established without it. |
| `hypothesis-missing: generalizes` | A source hypothesis has no counterpart, yet the Lean statement is proved (its axioms carry no `sorry`) and every instance of the source is an instance of it: a strictly more general theorem. State in the detail line why the source's objects satisfy the Lean's hypotheses. |
| `hypothesis-added: implicit` | A Lean hypothesis the source uses without stating. Not penalized. |
| `hypothesis-added: content` | A Lean hypothesis that assumes what the source proves or defines, such as an identity, a well-definedness fact, or a property of an object the source constructs. |
| `conclusion-weaker` / `conclusion-stronger` / `conclusion-different` | The conclusion says less, more, or something else. Existence in place of unique existence is `conclusion-weaker`. |
| `conclusion-stronger: proved` | The Lean concludes strictly more than the source, the source's conclusion follows from it, and the packet's axioms show a proof. A stronger true theorem: state in the detail line how the source's conclusion follows. |
| `quantifier` | Order, strength, or dependence of a quantifier changed. |
| `strictness` | Strict against non-strict, open against closed, positive against nonnegative. |
| `domain` | Type, domain, finiteness, or locality changed: a half-plane for the plane, the naturals for the integers, a bounded set for any set. |
| `definition-hollow` | A project definition that ignores a parameter, holds of everything or nothing, or is a name over a generic type. |
| `uninstantiated-structure` | A structure or class carrying the theorem's mathematical content as fields, with no inhabitant in the packet. The theorem is then conditional on an axiomatization. |
| `library-convention` | A library convention silently changes the meaning. |
| `none` | The cards agree. |

## Scores

The table is the same scale as the faithfulness rubric so scores compare
across the two, but here each score is bound to the list.

| Score | Bound to |
|---:|---|
| 5 | `none`. |
| 4 | Only `hypothesis-added: implicit`, `hypothesis-missing: generalizes`, or `conclusion-stronger: proved`, or implementation-level assumptions such as decidability or a harmless stronger typeclass. |
| 3 | Only differences you can show are equivalent: naming, coercions, an equivalent reformulation. State the equivalence in the detail line; if you cannot, it is not a 3. |
| 2 | Any plain `hypothesis-missing`, `hypothesis-added: content`, plain `conclusion-*`, `quantifier`, `strictness`, `domain`, or `library-convention`. |
| 1 | Any `object-substituted` or `uninstantiated-structure`, when the substituted or axiomatized part carries the source's content. |
| 0 | `definition-hollow` at the root, or a statement the attached findings show to be trivial: `definition-trivial`, or `hypothesis-unnecessary` with every hypothesis deleted. |

A statement takes the lowest score any of its discrepancies binds it to.

Anti-inflation guard: if your own detail lines say "meaningful", "significant",
"notable", or "not formally established", the score is at most 2. An
abstraction is not legitimate because the source's proof happens to be
algebraic; the statement's objects must be the source's objects.

Return `unknown` instead of a score when the passage is missing, the packet
cannot be read, or the two cannot be aligned at all. Pass at 4; reject at 2 or
below; 3 goes to a human.

## Output

One block per article, in this order, nothing else:

```text
declarations: <Lean names, comma-separated>
reference: source | article
source card:
  objects: …
  hypotheses: 1. … 2. … (implicit: …)
  conclusion: …
formal card:
  objects: …
  hypotheses: 1. … 2. …
  conclusion: …
discrepancies:
  - <category> — <one line>
score: <0–5 | unknown>
verdict: <one sentence, stating the binding discrepancy or "cards agree">
```

## Traps

- **Axioms in a structure.** A theorem quantified over a structure whose fields
  are the identities the source proves has moved the mathematics into the
  hypotheses. The proof beneath may be honest and short; the statement is not
  the source's. Score by the fields, not by the proof.
- **The name does the work.** A generic construction under a suggestive name is
  `object-substituted` unless the packet connects it to the source object.
- **`True` fields and always-true definitions.** A property defined as `True`
  makes every hypothesis built from it vacuous. The attached findings usually
  say so; the card must say so too.
- **Existence for uniqueness, local for global, weak for strict.** These are
  the quiet weakenings; check each connective, not the shape of the sentence.
- **A hypothesis the source never states but always uses** is `implicit`, not
  a penalty. Do not reward a formalization for matching an omission.
- **A partial formalization is a weakening.** When the article's declarations
  cover some items of a multi-part passage and not others, the conclusion is
  weaker than the passage cited. The remedy is at the article: cite the part
  formalized, or formalize the rest. Say which items are covered.
- **A dropped hypothesis is not always a weakening.** If the Lean proves the
  conclusion for a wider class, the theorem is stronger than the source's, and
  the reviewer decides whether that is wanted; it is `generalizes`, not a
  reject. But only when the packet's axioms show a proof and the source's
  setting really is a special case; a dropped hypothesis the conclusion needs
  is plain `hypothesis-missing`.
