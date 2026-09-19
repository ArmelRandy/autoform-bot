{imports}
-- Autoform skeleton probe. This file is a Python-format template: `{{`/`}}` are
-- literal braces and single-brace fields are filled by autoform_cli.skeleton.
-- It is written to a temporary file and run with `lake env lean` inside the
-- built project; it never modifies the project.
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Data.Json

open Lean Elab Command Meta Term

-- A reader must see what is quantified over: `∃ n : ℕ, …`, not `∃ n, …`.
set_option pp.funBinderTypes true
-- and where a cast lands: `(↑n : ℚ)`, not `↑n`, since `1 / ↑n` means something
-- else in `ℕ`.
set_option pp.coercions.types true

namespace AutoformSkeleton

/-- Constants that fix the *meaning* of `c`: its type always, and its value only
when `c` is a definition. A theorem's proof is never part of its meaning. -/
def meaningConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | some info            => info.type.getUsedConstants
  | none                 => #[]

/-- Fold generated companions -- constructors, projections, recursors, matchers,
equation lemmas -- onto the declaration a reader sees in the source. -/
partial def canonical (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo _)  => canonical env c.getPrefix
  | _ =>
    if let some info := env.getProjectionFnInfo? c then canonical env info.ctorName
    else if isAuxRecursor env c || isNoConfusion env c || Meta.isMatcherCore env c || c.isInternalDetail then
      if c.getPrefix != Name.anonymous && env.contains c.getPrefix then canonical env c.getPrefix else c
    else c

def kindOf (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some (.defnInfo _)   => if isInstanceCore env c then "instance" else "def"
  | some (.thmInfo _)    => "theorem"
  | some (.axiomInfo _)  => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.inductInfo _) => if isClass env c then "class" else if isStructure env c then "structure" else "inductive"
  | some (.ctorInfo _)   => "constructor"
  | some (.recInfo _)    => "recursor"
  | some (.quotInfo _)   => "quot"
  | none                 => "unknown"

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun idx => env.header.moduleNames[idx.toNat]!

def signatureOf (c : Name) : CommandElabM String := do
  let sig ← liftTermElabM (PrettyPrinter.ppSignature c)
  return sig.fmt.pretty 100

/-- First node of syntax kind `k` inside `stx`, depth-first. -/
partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx else stx.getArgs.findSome? (findKind? · k)

/-- The namespaces the file opens above `line`, from its `open …` commands. Their
scoped notation (`#s`, `n !`, `∑ x ∈ s, f x`) must be active for the statement to
parse; Lean records what a declaration means, not how its file was set up. -/
def openedNamespaces (lines : List String) (line : Nat) : List Name :=
  (lines.take (line - 1)).flatMap fun l =>
    let l := l.trimAsciiStart.toString
    if l.startsWith "open " then
      ((l.drop 5).toString.splitOn " ")
        |>.filter (fun t => t ≠ "" && t ≠ "scoped" && t ≠ "in")
        |>.takeWhile (fun t => t ≠ "hiding" && t ≠ "renaming" && !t.startsWith "(")
        |>.map String.toName
    else []

/-- The declaration's source up to its value: the statement as written, without
the proof. Parsed with Lean's own parser rather than cut by pattern matching. -/
def statementSource (root : Name) : CommandElabM (Option String) := do
  let env ← getEnv
  let some r ← findDeclarationRanges? root | return none
  let some idx := env.getModuleIdxFor? root | return none
  let mod := env.header.moduleNames[idx.toNat]!
  let sp ← getSrcSearchPath
  let some path ← sp.findWithExt "lean" mod | return none
  let text ← IO.FS.readFile path
  let lines := text.splitOn "\n"
  let snippet := "\n".intercalate (lines.drop (r.range.pos.line - 1) |>.take (r.range.endPos.line - r.range.pos.line + 1))
  for ns in openedNamespaces lines r.range.pos.line do
    if env.isNamespace ns then activateScoped ns
  let env ← getEnv
  match Parser.runParserCategory env `command snippet with
  | .error _ => return none
  | .ok stx =>
    let decl := (findKind? stx ``Parser.Command.declaration).getD stx
    let val := (findKind? decl ``Parser.Command.declValSimple).orElse fun _ =>
      (findKind? decl ``Parser.Command.declValEqns).orElse fun _ => findKind? decl ``Parser.Command.whereStructInst
    let some v := val | return none
    let some pos := v.getPos? | return none
    -- `pos` is a byte position: cut by bytes, not by characters, or every `∀`
    -- before the value pushes the cut past it.
    let bytes := snippet.toUTF8.extract 0 pos.byteIdx
    return some ((String.fromUTF8! bytes).trimAsciiEnd.toString)

def rangeJson (c : Name) : CommandElabM Json := do
  match ← findDeclarationRanges? c with
  | some r => return Json.arr #[r.range.pos.line, r.range.endPos.line]
  | none   => return Json.null

def emit (root : Name) (fields : List (String × Json)) : CommandElabM Unit :=
  IO.println s!"{marker}{{(Json.mkObj (("root", Json.str (toString root)) :: fields)).compress}}"

def skeleton (projectRoots : List Name) (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    emit root [("found", Json.bool false)]
    return
  let isLocal (n : Name) : Bool :=
    match moduleOf env n with
    | some m => projectRoots.contains m.getRoot
    | none   => false
  let isCore (n : Name) : Bool :=
    match moduleOf env n with
    | some m => [{core_roots}].contains m.getRoot
    | none   => true
  -- A projection from a class onto a parent class, such as `Preorder.toLE`, is
  -- the path Lean walks to reach `≤` from the class a binder names. The reader
  -- trusts the class that is named, not the ancestors it happens to extend.
  let isClassProjection (e : Name) : Bool :=
    match env.getProjectionFnInfo? e with
    | some info => info.fromClass
    | none      => false
  -- Direct meaning-dependencies of a *folded* declaration are the union over
  -- everything that folds onto it, so a structure depends on what its fields
  -- mention even though only the constructor's type says so.
  let expand (c : Name) : Array Name := Id.run do
    let mut out : Array Name := #[]
    let mut work : Array Name := #[c]
    let mut seen : Array Name := #[]
    while h : work.size > 0 do
      let d := work[work.size - 1]
      work := work.pop
      if seen.contains d then continue
      seen := seen.push d
      for e in meaningConstants env d do
        let f := canonical env e
        if f == c then
          -- a generated companion of `c` itself: walk into it, do not list it
          if !seen.contains e then work := work.push e
        else if !isLocal f && isClassProjection e then
          continue
        else if !out.contains f then
          out := out.push f
    return out
  let mut trusted : Array Name := #[]
  let mut edges : Array (Name × Array Name) := #[]
  let mut assumed : Array Name := #[]
  let mut work : Array Name := #[root]
  while h : work.size > 0 do
    let c := work[work.size - 1]
    work := work.pop
    let mut localDeps : Array Name := #[]
    for d in expand c do
      if isLocal d then
        if !localDeps.contains d then localDeps := localDeps.push d
        if !trusted.contains d && d != root then
          trusted := trusted.push d
          work := work.push d
      else if !isCore d && !d.isInternalDetail && !isInstanceCore env d && !assumed.contains d then
        assumed := assumed.push d
    edges := edges.push (c, localDeps.qsort Name.lt)
  let axioms ← collectAxioms root
  let mut items : Array Json := #[]
  for c in trusted.qsort Name.lt do
    let deps := (edges.find? (·.1 == c)).map (·.2) |>.getD #[]
    items := items.push <| Json.mkObj [
      ("name", Json.str (toString c)),
      ("kind", Json.str (kindOf env c)),
      ("module", Json.str (toString ((moduleOf env c).getD Name.anonymous))),
      ("range", ← rangeJson c),
      ("signature", Json.str (← signatureOf c)),
      ("depends", Json.arr (deps.map fun d => Json.str (toString d)))]
  let rootDeps := (edges.find? (·.1 == root)).map (·.2) |>.getD #[]
  let statement := match ← statementSource root with | some s => Json.str s | none => Json.null
  emit root <| [
    ("found", Json.bool true),
    ("statement_source", statement),
    ("kind", Json.str (kindOf env root)),
    ("module", Json.str (toString ((moduleOf env root).getD Name.anonymous))),
    ("range", ← rangeJson root),
    ("signature", Json.str (← signatureOf root)),
    ("depends", Json.arr (rootDeps.map fun d => Json.str (toString d))),
    ("trusted", Json.arr items),
    ("assumed", Json.arr ((assumed.qsort Name.lt).map fun d => Json.str (toString d))),
    ("axioms", Json.arr ((axioms.qsort Name.lt).map fun d => Json.str (toString d)))]

end AutoformSkeleton

set_option maxHeartbeats 0 in
run_cmd do
  let projectRoots : List Name := [{project_roots}]
  for root in [{roots}] do
    AutoformSkeleton.skeleton projectRoots root
