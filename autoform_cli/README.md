# Blueprint format and CLI

The Autoform CLI validates, visualizes, and publishes the multilevel dependency
graph embedded in `blueprint/roadmap/`. The Markdown book is the graph: no
separate authored or generated graph file exists.

## Articles and containment

Every Markdown file below `blueprint/roadmap/` is an article node. A
`README.md` represents its directory and strictly contains the articles below
it; the nearest ancestor `README.md` is the single parent. This supports any
number of levels, from book to chapter to section to declaration. Ordinary
files use their path without `.md` as a stable ID; `README.md` uses its
directory path, with the root article named `roadmap`.

The H1 is the article's human title. Container
prose supplies the mathematical exposition, and a standalone list item linking
to a formalizable leaf places that definition or result at the exact position in
the published chapter. Leaves without a placement slot appear under an explicit
“Additional formalization targets” section rather than disappearing.

Keep the root roadmap article short: it is the book's preface and table of
contents, not a dump of every planned milestone. Large planning inventories
belong in coverage or progress views; detailed containers should introduce their
mathematics in prose and place statements under meaningful section headings.

Frontmatter records checked facts:

```markdown
---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MyProject.separatingHyperplane
---

# Separating hyperplane theorem

State the intended result and proof sketch here.

## Depends on

- [Convex set](convex.md)

## Proof depends on

- [Supporting hyperplane](supporting-hyperplane.md)

## Sources

- [Chapter 2](../../sources/convexity.md#separation)
```

`## Depends on` lists what the article needs in order to be *stated*;
`## Proof depends on` lists what only its *proof* needs. Both are graph edges.
Links anywhere else are ordinary navigation or citations. Dependencies resolve
relative to the current article and must point at another roadmap article.

The optional `declaration` field marks a formalizable leaf and describes its
intended Lean artifact, for example `def`, `theorem`, `lemma`, `structure`, or
`instance`. Container and exposition articles omit it. Autoform records this
hint but does not constrain the set of Lean declaration commands. Declarations
that introduce data rather than a proposition carry no separate proof
obligation.

`origin` records provenance for formalizable work: `cited` for a direct source
target, `bridged` for a result introduced between source targets, and
`background` for prerequisite mathematics.

Frontmatter is optional. A container article that only supplies prose and
placement needs none at all; only checked facts are recorded.

## Assertions and derived status

An article asserts only facts a human or agent verified:

| Key | Meaning |
| --- | --- |
| `statement: formalized` | The Lean statement exists and compiles. |
| `proof: formalized` | The Lean proof is complete. |
| `mathlib: true` | The result is upstreamed into Mathlib. |
| `not_ready: true` | Needs more blueprint work before it can be attempted. |
| `lean: Ns.decl` | Declaration name(s) that discharge the article. |
| `discussion: 42` | Issue number or URL where the article is being discussed. |
| `skeleton_approved: sha256:<64 hex>` | A person approved the statement's skeleton at this semantic hash. |
| `skeleton_evidence: sha256:<64 hex>` | The evidence hash of the joint packet that person read. |

Everything a reader thinks of as progress is *derived* from the DAG on every
run, so it cannot go stale:

| Derived state | Holds when |
| --- | --- |
| `can_state` | Every statement prerequisite is stated. |
| `can_prove` | Stated, and every proof prerequisite is proved. |
| `proved` | The proof compiles. |
| `fully_proved` | Proved, and every prerequisite is fully proved, recursively. |
| `defined` | A definition is written but rests on unfinished work. |

`proved` and `fully_proved` differ on purpose: a theorem whose own proof
compiles but which rests on an unproved lemma is green, not dark green. The
palette and state names follow
[leanblueprint](https://pypi.org/project/leanblueprint/), so the published
graph reads the same way as the Lean community's LaTeX blueprints.

## Commands

This section is the single source of truth for the command line. Skills
describe what to achieve and link here; they do not restate flags, so a change
to the CLI lands in one place.

The commands below are written as they appear on `PATH`. Inside a consumer
project the plugin is not installed, so resolve `<AUTOFORM_PLUGIN_ROOT>` from
the loaded plugin and prefix each one, running from the project root:

```bash
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform check blueprint --lean-root .
```

Create a new project's vault, site configuration, and CI. The layout is fixed,
so it is written rather than described; existing files are left alone, which
makes the same command the repair path:

```bash
autoform init . --title "Finite Flat Group Schemes" \
  --repository-url https://github.com/owner/repo
```

Pass `--autoform-ref <sha>` to pin the generated workflows at an immutable
commit, `--force` to overwrite, and `--json` for machine-readable output.

Publishing a project runs four steps in order: validate, write the Mermaid
graph into the vault, render the site source, then strict-build the site.

```bash
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform check blueprint --lean-root .
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform-visualize blueprint
uv run --project "<AUTOFORM_PLUGIN_ROOT>" autoform render blueprint \
  --output site-src --lean-root . --require-declarations
uv run --with mkdocs --with mkdocs-material --with mkdocs-literate-nav \
  --with pymdown-extensions mkdocs build --strict
```

Drop `--require-declarations` when reviewing work in progress, where a
statement may name a Lean declaration that does not exist yet.

Validate structure, and optionally check that every `lean:` name really exists
in the project's Lean sources:

```bash
autoform check blueprint --lean-root .
autoform audit blueprint --lean-root .
```

`check` validates the graph contract. `audit` adds deterministic completeness,
provenance, coverage, checked-fact, and optional Lean-target checks. It is local
and read-only: it neither contacts network services nor writes findings back
into the blueprint. Pass `--json` for stable machine-readable output; a nonzero
exit status means the audit found at least one issue. The machine-checkable
`coverage/README.md` contract contains one `Area | Coverage | Evidence` table
with `MAPPED`, `DECOMPOSED`, `DEFERRED`, or `OUT` dispositions. `MAPPED` is
nonterminal; the other three explicitly disposition an area. Audit JSON includes
canonical rows, counts, and the exact coverage source hash, while
`publication.json` records aggregate counts without duplicating the authored
rows.

The contract is read as published Markdown and fails closed. A table inside an
HTML comment, a fenced block, or a four-space-indented block is documentation
rather than contract, and is not discovered at all. A closing fence must carry
nothing but its marker, so a table below ```` ``` trailing ```` stays inside the
code block for the checker exactly as it does for the reader.

Because hidden content ends a table for every renderer, a comment or code block
written *between* rows is reported rather than silently truncating the contract.
This holds for multi-line constructs too: a blank line inside a comment or fence
belongs to that construct rather than ending the table. Any row-shaped line
stranded below such a break is named, including malformed rows and rows written
without their outer pipes, since Python-Markdown accepts `A | OUT | reason` as a
row just as readily as the canonical form.

Whether the table publishes at all is settled by rendering the document and
looking for it, not by inspecting its two structural lines. That distinction
matters because a table's fate depends on its surroundings: a comment can break
the delimiter row while leaving its column count intact, and a paragraph running
straight into the header makes the whole thing one lazy paragraph. Both publish
nothing and both are rejected. A comment *inside* a header cell does still render,
so that contract stands. If the page publishes a contract table the audit does not
recognise -- one written without outer pipes, say -- it says so rather than
claiming there is no table.

Finding a matching header on the page is not enough to conclude it came from the
lines just read, and neither is finding matching rows. A canonical-looking table
that renders as a paragraph, sitting above an unrelated raw-HTML table with
identical rows, satisfies any comparison of values while publishing nothing
itself. So provenance is established rather than inferred: the source rows are
rendered again carrying a marker, and the published table has to be the one that
marker turns up in. The marker is grown until neither the source nor any
published cell contains it. Checking the source alone is not enough, because
rendering synthesises text the source never held literally: `&#97;utoform...`
and `autoform<span></span>...` both normalise to the same cell a reader sees. The
comparison is against published cell text, so that is what the marker has to be
absent from.

Substituting rows is only sound if it changes nothing else, which is not
something to assume: an unclosed `<style>` inside a row swallows the rest of the
document, so removing that row *exposes* tables the page never published, and one
of those can then supply the marker. So the trace has to leave the page's
topology intact -- same tables in the same order, same headers, identical rows
everywhere except the one position being traced. A row that fails this is
refused, and named as such, because the trace says nothing about a document the
substitution changed. One honest consequence: evidence that itself contains a raw
`<table>` disappears along with the row and is refused for the same reason. That
is fail-closed on a cell no contract needs, which is the right side to err on.

Only what a reader can see counts. Visibility propagates from ancestors, so a
table inside `<div hidden>` is no more published than one carrying `hidden`
itself; a hidden row drops out while its siblings remain; and a hidden cell is
treated as no column rather than an empty one, since keeping it invents a column
that both disguises a table whose visible headers match and manufactures
mismatches in one whose rows do. The boundary here is deliberate: hiding is read
from HTML, not from CSS. An element hidden by a stylesheet class or an inline
`display: none` still counts as published, because following that faithfully
would mean resolving the site's stylesheets, and a check that resolves them
badly is worse than one whose limit is written down.

Evidence must say something to a reader, judged on rendered text rather than
Markdown source. A cell holding only a code span, only a comment, only emphasis,
only an HTML tag, only an entity, or only an empty link such as `[ ](notes.md)`
is rejected: each carries word characters in the source and shows the reader
nothing. Text a browser hides is treated the same way. That check runs on an
HTML5 tree rather than on a pattern or a token stream, because what a reader ends
up seeing is decided by the repair a browser performs on malformed markup:
`<span hidden>reason` and `<span hidden />Reason` both stay hidden, since an
unclosed non-void element stays open, while `<p hidden>aside<p>Real reason` shows
its second paragraph, since that one implicitly closes the first. `title="hidden"`
hides nothing at all. So is evidence that is nothing but `TODO`, `TBD`, `pending`,
`placeholder`, or `unknown`, or that opens with one of those as a marker such as
`TODO: choose a milestone`. A status word that merely begins a sentence is fine:
"Pending Mathlib PR 1234" names something a reader can check. `DECOMPOSED`
evidence must contain at least one complete inline link to an existing roadmap
article, and *every* link it offers must resolve, fragments included, under the
same rules the audit applies. A link missing its closing parenthesis does not
render and does not count.

Fragment checking uses the renderer rather than predicting it. Anchors come from
running Python-Markdown with the extensions the generated `mkdocs.yml` enables
and reading the heading IDs back out of its HTML. Heading IDs turn out to depend
on much more than the heading line -- whether it sits in a blockquote or a list
item, whether a raw HTML block swallows it, how `attr_list` treats an escaped
brace, what `arithmatex` leaves behind for the slugger -- and every attempt to
predict that got some cases wrong in both directions. The extension list lives in
one place in Python, and a test binds it to the shipped `mkdocs.yml` so enabling
a heading-affecting extension cannot silently invalidate the audit.

### What coverage completeness does and does not claim

`coverage.complete` in audit and `publication.json` means exactly one thing:
every row the author declared has reached a terminal disposition, so no row is
still `MAPPED`. It is a statement about the contract, not a measurement of the
project.

It does **not** claim that the declared rows cover the source exhaustively, and
it says nothing about whether the linked roadmap articles are formalized or
proved. A project that declares one narrow area and disposes of it reports
`complete` while most of its source remains undeclared. Exhaustiveness is an
authoring judgement that no local check can make.

Publication and audit are deliberately different gates. The generated
`blueprint-pages.yml` runs `check` and `render`; it does not run `audit`. An
invalid coverage contract fails `render` before any output is written, but a
valid contract with `MAPPED` rows publishes normally even though `audit` reports
each one as a `declared-coverage-gap`. That is intended: a roadmap is published
while it is still being decomposed, and the published `coverage.complete: false`
is how a reader sees that. Run `autoform audit` in CI when you want mapped rows
to block a merge.

Extract what a reader must trust for each formalized statement:

```bash
autoform skeleton blueprint --lean-root .
autoform skeleton blueprint --lean-root . --node chapter/main-result
autoform skeleton blueprint --lean-root . --output skeleton.json --packets review-packets --passages review-passages
autoform skeleton blueprint --lean-root . --output skeleton.json --probe
```

A theorem means what its statement means. The skeleton of a `lean:`
declaration is the reading list a person needs to agree that the Lean says what
the article claims: the elaborated signature, then every project declaration
the *statement* rests on, transitively, quoted from the sources in dependency
order. A definition contributes its body as well as its type, because the body
is part of its meaning; a theorem met along the way contributes only its type.
Proofs are never entered. The proof beneath a skeleton may be orders of
magnitude longer, and it is the kernel's to check, not the reader's. Each
skeleton also reports the axioms the declaration finally rests on, so a `sorry`
shows up as `sorryAx` beside the statement rather than under it, and the
non-core constants it assumes from Mathlib or another dependency, listed by
name so a reader can see that a statement uses the library's notion of a limit
rather than a homemade one.

The closure is computed from elaborated terms, which is why this is the one
command that runs Lean: it writes a small probe and runs it with
`lake env lean` against the built project. Before the probe, Lake must confirm
without rebuilding that every imported module matches its exact source inputs;
a missing `lake-manifest.json`, stale artifacts, or a source tree that changes
during extraction makes the command fail. A lexical closure would
miss what
`open`, notation, implicit instances, and auto-bound variables bring in, and
every miss silently shrinks the surface a reader is told to trust. Constructors,
projections, recursors, matchers, and equation lemmas are folded onto the
declaration the reader sees in the source, so a structure appears once, as its
`structure` block. Names outside the project are the trusted base and are not
expanded. The command exits nonzero when a `lean:` name is absent from the
sources or from the built environment, and it writes nothing into the vault;
`--output` records the `autoform-skeleton/v2` report, which contains no
timestamp or absolute path, for a later render or review to consume. The
report quotes each trusted definition's source and records theorem
dependencies by elaborated signature, so it stands on its own without ever
copying a theorem proof.

Every skeleton carries a full SHA-256 **hash** of its meaning. It is derived
from canonical elaborated expressions for the root, every trusted declaration,
each direct external assumption, and each axiom, together with the dependency
edges, Lean version, and compiled-module identities for the transitive external
boundary. Local source spelling and comments do not enter the semantic hash,
while macro expansion, synthesized instance bodies, types, and definition
bodies do. Because external modules are bound as compiled artifacts, an
unrelated change in one of those modules may conservatively rotate the hash.
An article with several `lean:` names has one hash over all of them, printed as
the article skeleton. The hash is how packets and reports are compared across
builds, and testimony written about a packet can name the skeleton it was
written about.

Reports and packet manifests also carry an evidence hash over the exact
proof-free text shown to a reviewer. Semantic hashes survive presentation-only
edits; evidence hashes ensure an approval is attached to the bytes that were
actually reviewed. An article review hash additionally binds the joint packet
to the cited passage and its locator. Two kinds of testimony are pinned to
these hashes:

- **Approval.** When a person has compared the book statement with the
  skeleton and agreed that the Lean says what the book says, the article
  records `skeleton_approved: <article hash>`, the semantic hash, and
  `skeleton_evidence: <article evidence hash>` for the exact joint packet
  that was read. Both are assertions, so they live in frontmatter like every
  other checked fact; the evidence key is optional, the semantic key is not.
- **Read-backs.** An independent agent that has seen only one declaration's
  packet writes what it literally asserts, in mathematical English, and files
  it as `blueprint/readbacks/<article id>/<Lean name>.md` with `declaration`,
  `skeleton` (the semantic hash), `packet` (the evidence hash of the packet it
  read), and `model` frontmatter. Read-backs are testimony, not derived
  state, so they are committed with the book. The
  [read-back reference](../skills/human-review/references/readback.md) gives
  the auditor its instructions; the practice follows Prove2me's mission audits.

`--packets DIR` writes one comment-stripped packet per skeleton, with a
manifest mapping packets to articles and hashes. The destination must be empty
or carry Autoform's packet manifest; each run replaces the complete managed
tree, so removed declarations cannot leave stale packets behind. A concurrent
change to the existing tree aborts publication instead of being overwritten.
A packet holds only what a blind auditor may see: the signature, the statement
as written, and the source of every project definition it rests on, with every
comment and docstring removed, so that a reader who is asked what the Lean
literally asserts cannot read the author's intent into it.

`--probe` adds three kernel-checked tests to the report. They are one-sided:
a success is a finding, a failure says only that cheap automation did not get
through, which is the expected case. Each attempt runs in an empty context
under a heartbeat budget a tenth of Lean's default, with a fixed sweep of
tactics (`rfl`, `trivial`, `simp`, `simp_all`, `omega`, `decide`, `exact?`,
and with Mathlib also `norm_num`, `positivity`, `linarith`, `nlinarith`,
`aesop`).

- **Necessity probes** delete each propositional hypothesis of a theorem in
  turn, and then all of them, and try to prove what remains. A success means
  the conclusion did not need that hypothesis: either the book's hypothesis is
  redundant, which is rare and worth knowing, or the formal conclusion is not
  the book's. Reported as `hypothesis-unnecessary`.
- **Definition checks** apply to propositional definitions: whether the
  unfolded body holds of every input or of no input (`definition-trivial`),
  whether an explicit argument is never used (`definition-unused-argument`),
  and whether a clause of a conjunction follows from the others
  (`definition-redundant-clause`). A degenerate definition also shows up in
  every theorem that uses it, since a vacuous hypothesis is always deletable.
- **Witnesses** are declarations named `<Def>.witness`, whose type ends in an
  application of the definition, and `<Def>.counterexample`, whose type ends
  in its negation, anywhere in the library. The report says whether each is
  found, missing, of the wrong shape, or proved with `sorry`. A missing one is
  advisory, because existence can be a hard theorem in its own right; a filed
  one that is wrong is `witness-invalid`. The negative witness is the one that
  catches vacuity and is almost always the easy one.

Each theorem's packet also carries the statement *as written*, cut before its
value by Lean's parser with the file's opened namespaces in scope so that
scoped notation parses, beside the elaborated signature: the printed form
shows binders that `variable` and `include` inject and the type every cast
lands in, the written form shows what the pretty-printer elides, and neither
can hide what the other shows.

A statement's source passage can travel with it. A `## Sources` link to a
non-Markdown file inside the blueprint with a `#L<start>-L<end>` fragment, for
example `../../../sources/lebl-ra/ch-real-nums.tex#L693-L714`, names the exact
text the statement came from. `--passages DIR` writes those passages beside
the packets, one per article, in a separate, disjoint managed directory. It
requires `--packets`. Each article directory
also holds `article.lean`, the joint packet of every declaration the article
names, because a source theorem is often formalized by several declarations
together and each alone is honestly incomplete. A faithfulness judge is given
the article packet and its passage; a read-back auditor is given one
declaration's packet alone, since a read-back is testimony about one
declaration.

`--mutants DIR` writes a calibration set for a faithfulness judge. Every
statement is printed in one uniform elaborated form, and beside it every
known-wrong variant the generator can make on the elaborated term: a
propositional hypothesis dropped, `<` for `≤` and back, `∃` for `∀` and back
on an object binder, `∧` for `∨` and back, the sides of a subtraction or
division swapped, a numeral raised by one, the conclusion negated, a conjunct
dropped, and for a propositional definition its body replaced by `True`. Every
mutant typechecks by construction. Some are accidentally equivalent to the
original, swapping the sides inside `|a - b|` for one; the generator tries to
prove `original ↔ mutant` with the probes' cheap sweep and marks the ones it
can, so detection rates are read net of them, and the rest are visible when
reading the ones a judge misses. The unit of the set is the article, with one
declaration mutated at a time. No harness packet lists axioms: a mutant is
unproved by construction, and copying the original's axioms would let a
dropped hypothesis pass as a kernel-proved generalization, so the rubric's
two generalization rules do not apply in the harness and a real
generalization in an original counts as a false alarm the report can see.
Declarations that are never mutated, structures and data-valued definitions,
appear in the blind form with their fields and bodies. Packets
are named opaquely with the passage beside each, and `labels.json` is the
answer key a judge must never see. Judging originals and mutants alike, then
scoring against the key, measures which operations the judge is blind to and
binds each score on its scale to the changes it actually detects.

`autoform audit … --skeleton skeleton.json` compares both with the current
report: `skeleton-drift` names an approval whose skeleton meaning has moved,
`skeleton-evidence-drift` one whose recorded packet text has, and
`readback-stale`, `readback-revised`, or `readback-missing` names testimony
whose skeleton moved, whose packet text changed, or that was never filed. The probe findings above are reported beside them. `autoform render … --skeleton skeleton.json` adds a
*Review* disclosure under every statement box, showing the skeleton, the
assumed library notions, the axioms, the read-back with its currency, and the
approval state, so a reviewer compares book text, Lean, and testimony without
leaving the page. Read-backs are never published as pages of their own.

Plan durable article identity metadata without changing the blueprint:

```bash
autoform migrate article-ids blueprint --json
autoform migrate article-ids blueprint --check
```

`article_id` accepts opaque values in the form `af_` plus 24 lowercase hex
digits. The planner validates uniqueness, proposes deterministic IDs for
missing articles, includes exact source hashes, and is strictly read-only.
Applying plans, moving runtime consumers and claims to durable IDs, and
preserving publication routes are intentionally deferred to follow-up changes.

Coordinate temporary cross-machine ownership without modifying the book:

```bash
export AUTOFORM_WORKER_ID="agent-name"
autoform claim acquire "chapter/main-result"
autoform claim renew "chapter/main-result"
autoform claim release "chapter/main-result"
```

Claims are fail-closed compare-and-swap leases under
`refs/autoform-claims/` on the Git `origin`; pass `--repo` for another claim
board. A failed acquire or renew means the caller cannot prove ownership and
must stop before committing or pushing protected work. Claims do not prove
mathematical correctness and do not replace branch-level Git CAS.

Write the Mermaid dependency graph into the vault, where Obsidian renders it:

```bash
autoform-visualize blueprint
```

Build the publishable site source — a book overview, aggregate progress,
statement boxes with collapsed dependency details, multi-scale dependency
maps, and direct links to Lean declarations at the current commit:

```bash
autoform render blueprint --output site-src --lean-root . --require-declarations
```

`render` never writes into the vault. It leads the landing page with the project
map over a summary of what is formalized and what is unblocked, places a compact
progress summary after each chapter's opening prose, writes `structure.md` so a
vault's layout can be checked against the book it produces, and shows a source
icon when a `lean:` declaration resolves to a repository permalink. Its
`dependencies.md` entry point rolls dependencies through the article hierarchy,
with links to declaration maps, one-hop local contexts, and the complete DAG.
Every graph article returns to the book, and every formal statement links to
its local context. Point `mkdocs.yml` at `docs_dir: site-src` and enable
`md_in_html` plus a `pymdownx.superfences` mermaid fence; see the [repository
example](../skills/setup/assets/cabannes-thesis-project/mkdocs.yml).

## Validation

`autoform check` rejects cycles, missing targets, escaping paths,
self-dependencies, cycles introduced at any rolled-up containment level,
missing or multiple H1 titles, unsupported frontmatter keys, and assertion
values it does not recognize. With `--lean-root` it also fails on a `lean:` name
absent from the sources, as `leanblueprint checkdecls` does for LaTeX
blueprints. It validates structure and leaves mathematical correctness to the
agent and the Lean kernel.

The Markdown files are the source of truth. Graphs and sites are derived views
that may be regenerated at any time.

## Audit contract

`autoform audit` reports structured findings at blueprint-relative paths. It
checks that formalizable articles are declaration-sized leaves with statement
text and an explicit dependency section, that asserted proof and Mathlib facts
are internally consistent, and that cited work resolves to local source
material without escaping the blueprint. Coverage files are checked for broken
links and explicitly declared gaps. With `--lean-root`, local declaration names
and declaration kinds are checked against the Lean source index.

### Structure

Containment is inferred from nested `README.md` articles, so a chapter
directory without one is invisible to the hierarchy: its pages attach to the
roadmap root and the book loses a level. `missing-chapter-article` reports a
directory directly under `roadmap/` that holds articles but names no chapter.
Deeper directories (the `definitions/` and `theorems/` buckets the bundled
example uses) are a filing convention inside a chapter and are not checked.
`overfull-container` reports an article with more than 24 direct children,
which is a table of contents rather than a chapter. Both defects leave a valid
graph, which is why they need their own checks rather than falling out of
`autoform check`.

### Node size

`node-too-large` is retrospective and needs `--lean-root`: it measures the
source span of a node's resolved `lean:` declarations, from each declaration's
first line to the line before the next one. A node is reported only once it
clears both 200 lines and four times this project's own median, so a project
whose units are uniformly long is measured against itself rather than gated on
an imported norm, and a project with too few finished nodes to have a
meaningful median cannot clear the multiple at all. Every measurement appears
in the finding's reason, so `--json` over a finished project is also the
calibration corpus for the threshold.

Nothing authored in an article predicts this. On the 43 finished nodes of
[`phulin/finite-flat`](https://github.com/phulin/finite-flat), prose length
correlates with realized Lean length at r = -0.03 and prerequisite count at
r = 0.25; its largest node is 1344 lines of Lean behind 66 words of prose and a
single declaration name. Pre-formalization size estimates were considered and
rejected on that evidence.

The audit API also accepts an already compiled graph. Future orchestration may
turn its findings into private work items, but the audit itself never enqueues
work, stamps articles, or creates another graph artifact.

## Claim contract

Claims use canonical `autoform-claim/v1` JSON in orphan commit messages and
exact observed object IDs as update preconditions. Absent and verifiably expired
leases may be acquired; live peer leases are refused. Malformed or unreadable
refs are unverifiable and may not be acquired, renewed, released, or removed by
cleanup. A heartbeat verifies ownership on entry and permanently records any
later refusal or transport uncertainty as lost ownership.

A claim key is a slug and digest of any string, not a validated node id, so a
shared resource is locked the same way a node is. Parallel agents get one Git
worktree each and serialize `lake build` behind a `lake-build` claim, because
builds share the elan toolchain and the Mathlib cache even when the checkouts
are separate.

Claims are temporary operational state, never article frontmatter. Future
Deicyde workers may share this protocol, but their current continue-uncoordinated
failure behavior must be removed before they use the canonical claim API.

## Local runtime doctor

Use the runtime projection and roadmap audit together without contacting any
external service:

```bash
autoform doctor . --lean-root .
autoform doctor blueprint --json
```

The doctor reports six ordered checks: blueprint resolution, runtime schema,
graph counts, reference invariants, roadmap audit, and optional local Lean
targets. It exits zero only when every required check passes. Omitting
`--lean-root` records an explicit advisory pass; supplying it performs only a
lexical local-source check, not a Lean build, kernel check, or proof-honesty
review. The bundled example intentionally exits nonzero while its declared
coverage still holds `MAPPED` rows.

This command is strictly read-only and local. It does not invoke Git, GitHub,
subprocesses, network services, claims, queues, reviews, recovery state,
providers, workers, renderers, or dashboards, and it creates no cache, scratch
repository, service, state directory, or `graph.json`. It is a project/runtime
doctor, separate from any future Deicyde fleet or machine-capability preflight.

## Runtime contract

`autoform_cli.runtime` projects the canonical Markdown graph into the versioned,
deeply immutable in-memory schema `autoform-runtime/v1`. Its declared authority
is `markdown-articles`: the adapter copies hierarchy, typed statement and proof
dependencies, authored assertions, derived progress, provenance, and optional
local Lean source locations, but it provides no persistence or write API.
`RuntimeGraph.as_dict()` and `to_json()` are deterministic compatibility
snapshots for consumers, not an authored or generated graph file. Autoform never
creates, synchronizes, or treats `graph.json` as an authority.

Every article remains in the runtime view so consumers can preserve the book's
arbitrary containment hierarchy. A node is dispatchable only when it is both a
formalizable article and a leaf; narrative containers and prose-only leaves are
never proof work units. The source revision hashes exact roadmap article paths
and bytes, excluding timestamps, absolute paths, Git state, and operational
state. Optional Lean locations come from a local lexical scan and do not by
themselves establish compilation or proof correctness.

Schema v1 retains the graph's path-derived article ID. That is suitable for
an ephemeral runtime projection and temporary claims, but it is not yet an
approved durable identity. Queues, reviews, recovery records, PR markers,
dashboard routes, providers, and logs must not persist against this ID until a
path-move identity and migration policy is defined. Those records remain private
and excluded from runtime snapshots and publication.

## Publication contract

`autoform render` publishes the book, derived progress, and dependency maps at
project, chapter, nested-scope, local, and full-graph scales. It never reads a
`graph.json` or an operational queue. Hidden files are omitted, while symlinks,
credentials, logs, provider state, and agent/task state inside the blueprint
cause the render to fail rather than silently leak them. Source and output
directories must be disjoint.

Every render writes `publication.json` with the source-content hash, Git ref,
article and dependency counts, and available views. It contains no timestamp or
absolute path, so identical inputs produce identical output files.
