---
name: human-review
description: >-
  Prepare and guide human inspection of an Autoform roadmap or formalization
  through its Obsidian graph and rendered blueprint site. Use when a person wants
  to browse, approve, reject, or discuss scope, dependencies, progress, source
  links, or Lean artifacts visually; do not substitute an autonomous agent
  verdict for the human's judgment.
---

# Prepare a human review

Inspect the repository without changing mathematical content. Require an
existing Autoform vault and site configuration; hand missing infrastructure to
Setup. Keep the Markdown vault as the source of truth and regenerate only
derived review views.

Regenerate the review views from `<PROJECT>`: validate the blueprint, refresh
the Mermaid graph with `autoform-visualize` so Obsidian shows current
dependencies, render the site source, then strict-build the site. Follow the
publication sequence in the [CLI reference](../../autoform_cli/README.md#commands),
but omit `--require-declarations`: review happens while statements are still
unformalized, and a missing declaration is something for the reviewer to see
rather than a reason to refuse to render.

Stop on structural failures and present them before asking for mathematical
judgment. For vault review, point the user to `blueprint/README.md`, coverage,
chapter pages, and `blueprint/dependencies.md` in Obsidian. For browser review,
serve the built site over localhost and provide the overview, progress, project
graph, relevant chapter graph, and node-neighborhood links.

Guide the review from coarse to fine: declared scope and exclusions, milestone
book, progress summary, cross-chapter graph, chapter graph, then individual node
and Lean-source links. Record each human decision as `approve`, `revise`, or
`block`, with the exact page or node and rationale. Separate validator output
from the person's judgment. Do not silently apply requested revisions: hand
mathematical-plan changes to Roadmap, Lean implementation changes to
Orchestrate, and autonomous rubric scoring to Agent Review.

## Review formalized statements through skeletons and read-backs

A compiled proof says nothing about whether the statement means what the book
says. The person reviews the *skeleton* instead: the elaborated signature and
the project definitions it rests on, a few lines per result, and beside it a
*read-back*, a blind rendering in mathematical English of what that skeleton
literally asserts. The reviewer compares the book statement, the skeleton, and
the read-back on one screen; the kernel covers everything below.

1. Extract the skeletons from the built project and write the blind packets,
   with the `skeleton` command in the [CLI reference](../../autoform_cli/README.md#commands):
   `autoform skeleton blueprint --lean-root . --output skeleton.json --packets review-packets --probe`.
   `--probe` runs the necessity probes, definition checks, and witness lookups;
   it is slower, and its successes are the statements to show the person
   first, since each one is a hypothesis the Lean did not need or a definition
   that holds of everything or nothing. Ask the formalizer, not the reviewer,
   to file `<Def>.witness` and `<Def>.counterexample` declarations for each
   definition; a definition with no counterexample is a question for the
   reviewer, not a failure.
2. Obtain a read-back for every packet that has none or is stale. Never write
   one yourself: you know what the code is meant to say. For each packet,
   launch an independent sub-agent with a fresh context and give it only that
   declaration's packet file and [the read-back reference](references/readback.md); file its
   testimony under `blueprint/readbacks/<article id>/<Lean name>.md` with the
   skeleton hash from the packet manifest and the model's name.
3. Render with the report, `autoform render … --skeleton skeleton.json`, and
   strict-build the site. Every statement box gains a *Review* disclosure with
   the skeleton, the assumed library notions, the axioms, the read-back, and
   the approval state.
4. Walk the person through each statement: book text first, then the
   read-back, then the skeleton. Ask whether the read-back says what the book
   says, whether any hypothesis is missing or added, and whether the
   definitions mean what the book's do. When they approve, record it as a
   checked fact in the article's frontmatter, `skeleton_approved: <hash>`,
   with the article hash the report shows; this is the one vault write review
   makes, and it is the person's assertion, not yours. When they do not,
   record `revise` with their reason and hand the change to Roadmap or
   Orchestrate.
5. Run `autoform audit blueprint --skeleton skeleton.json` before reporting.
   It names every approval whose skeleton has since moved (`skeleton-drift`)
   and every read-back that is missing or stale, so an edit to a statement can
   never keep an approval it was not given.
