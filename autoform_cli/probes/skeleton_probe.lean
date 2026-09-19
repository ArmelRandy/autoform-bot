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

namespace AutoformProbe

/-! Necessity probes and definition checks: one-sided, kernel-checked tests of
whether a statement is easier than it should be. A success is a finding; a
failure says nothing. Every attempt runs under its own heartbeat budget in an
empty local context, so no deleted hypothesis can be used by accident. -/

def budget : Nat := {budget} * 1000

def tactics : TermElabM (List (String × Syntax)) := do
  return [{tactics}]

/-- Try each tactic on a fresh goal of `type`; return the first that closes it. -/
def attempt (type : Expr) : TermElabM (Option String) := do
  for (name, tac) in ← tactics do
    let saved ← saveState
    let ok ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => {{ ctx with maxHeartbeats := budget }}) <| Core.withCurrHeartbeats do
        withLCtx {{}} {{}} do
          let mvar ← mkFreshExprMVar type
          Term.runTactic mvar.mvarId! tac .term
          let value ← instantiateMVars mvar
          pure (!value.hasExprMVar && !value.hasSorry))
      (fun _ => pure false)
    restoreState saved
    if ok then return some name
  return none

/-- Universe parameters instantiated at `Type`, so `Sort u` never collapses to `Prop`. -/
def fixLevels (n : List Name) : List Level := n.map fun _ => Level.succ Level.zero

def resultJson (result : Option String) : Json :=
  match result with | some t => Json.str t | none => Json.null

/-- Delete each propositional hypothesis in turn, then all of them, and try to
prove what remains. -/
def hypothesisProbes (root : Name) : TermElabM (Array Json) := do
  let some info := (← getEnv).find? root | return #[]
  unless info matches .thmInfo _ | .axiomInfo _ do return #[]
  let type := info.type.instantiateLevelParams info.levelParams (fixLevels info.levelParams)
  let goals ← forallTelescope type fun fvars body => do
    let mut props : Array Expr := #[]
    for fv in fvars do
      if ← isProp (← inferType fv) then props := props.push fv
    let mut goals : Array (String × String × Expr) := #[]
    let build (dropped : Array Expr) : TermElabM (Option Expr) := do
      let keep := fvars.filter fun f => !dropped.contains f
      let goal ← mkForallFVars keep body
      if goal.hasAnyFVar (fun id => dropped.any fun d => d.fvarId! == id) then return none
      return some goal
    for fv in props do
      let decl ← fv.fvarId!.getDecl
      if let some goal ← build #[fv] then
        goals := goals.push (decl.userName.toString, toString (← ppExpr decl.type), goal)
    if props.size > 1 then
      if let some goal ← build props then
        goals := goals.push ("*", "every hypothesis", goal)
    return goals
  let mut out := #[]
  for (name, ty, goal) in goals do
    let result ← attempt goal
    out := out.push <| Json.mkObj [("hypothesis", name), ("type", ty),
      ("statement", toString (← ppExpr goal)), ("proved", Json.bool result.isSome),
      ("tactic", resultJson result)]
  return out

partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then e.appFn!.appArg! :: conjuncts e.appArg! else [e]

/-- For a propositional definition: does it hold of everything, of nothing, does
it ignore an explicit argument, and is any clause implied by the others? -/
def definitionChecks (root : Name) : TermElabM (Array Json) := do
  let some (.defnInfo v) := (← getEnv).find? root | return #[]
  let value := v.value.instantiateLevelParams v.levelParams (fixLevels v.levelParams)
  let goals ← lambdaTelescope value fun fvars body => do
    unless ← isProp body do return #[]
    let mut goals : Array (String × String × Expr) := #[]
    goals := goals.push ("always", "holds of every input", ← mkForallFVars fvars body)
    goals := goals.push ("never", "holds of no input", ← mkForallFVars fvars (mkNot body))
    let parts := (conjuncts body).toArray
    if parts.size > 1 then
      for i in [0:parts.size] do
        let mut others : Array Expr := #[]
        for j in [0:parts.size] do
          if j != i then others := others.push parts[j]!
        let hyp := others[1:].foldl (fun acc p => mkAnd acc p) others[0]!
        let goal ← mkForallFVars fvars (← mkArrow hyp parts[i]!)
        goals := goals.push ("redundant-clause", toString (← ppExpr parts[i]!), goal)
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if decl.binderInfo.isExplicit && !body.containsFVar fv.fvarId! then
        let usedLater ← fvars.anyM fun g => do pure ((← inferType g).containsFVar fv.fvarId!)
        unless usedLater do
          goals := goals.push ("unused-argument", decl.userName.toString, mkConst ``True)
    return goals
  let mut out := #[]
  for (kind, detail, goal) in goals do
    let result ← if kind == "unused-argument" then pure (some "syntactic") else attempt goal
    out := out.push <| Json.mkObj [("kind", kind), ("detail", detail),
      ("holds", Json.bool result.isSome), ("tactic", resultJson result)]
  return out

partial def stripToHead (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``Exists 2 then
    lambdaTelescope e.appArg! fun _ b => stripToHead b
  else if e.isForall then forallTelescope e fun _ b => stripToHead b
  else return e

/-- A witness is any declaration named `<root>.witness` whose type ends in an
application of the definition; a counterexample, `<root>.counterexample`, ends
in its negation. Both are checked for shape and for `sorry`. -/
def witness (root : Name) (suffix : String) (negative : Bool) : TermElabM Json := do
  let name := root ++ Name.mkSimple suffix
  let env ← getEnv
  let status ← match env.find? name with
    | none => pure "missing"
    | some info => do
      let head ← stripToHead info.type
      let shape := if negative then head.isAppOfArity ``Not 1 && head.appArg!.getAppFn.constName? == some root
                   else head.getAppFn.constName? == some root
      let axioms ← collectAxioms name
      pure (if !shape then "mismatched" else if axioms.contains ``sorryAx then "sorry" else "found")
  return Json.mkObj [("role", if negative then "counterexample" else "witness"),
    ("name", toString name), ("status", status)]

def report (root : Name) : CommandElabM (List (String × Json)) := do
  let env ← getEnv
  let isDefinition := match env.find? root with | some (.defnInfo _) => true | _ => false
  let probes ← liftTermElabM (hypothesisProbes root)
  let checks ← liftTermElabM (definitionChecks root)
  let witnesses ← if isDefinition then do
      pure #[← liftTermElabM (witness root "witness" false), ← liftTermElabM (witness root "counterexample" true)]
    else pure #[]
  return [("probes", Json.arr probes), ("checks", Json.arr checks), ("witnesses", Json.arr witnesses)]

end AutoformProbe

namespace AutoformMutate

/-! Known-wrong variants of a statement, made on the elaborated term so every
mutant typechecks by construction. They calibrate a faithfulness judge: each
mutant differs in meaning from the original by one named operation, so a judge
that scores it like the original is blind to that operation. -/

/-- Replace the `target`-th occurrence, in pre-order with binders instantiated,
of a subterm `pick` accepts. -/
def replaceNth (e : Expr) (pick : Expr → MetaM (Option Expr)) (target : Nat) :
    MetaM (Option Expr) := do
  let counter ← IO.mkRef 0
  let hit ← IO.mkRef false
  let r ← Meta.transform e (pre := fun sub => do
    match ← pick sub with
    | some rep =>
      let k ← counter.get
      counter.set (k + 1)
      if k == target then
        hit.set true
        return .done rep
      return .continue
    | none => return .continue)
  if ← hit.get then return some r else return none

def allMutants (e : Expr) (pick : Expr → MetaM (Option Expr)) (limit : Nat := 4) :
    MetaM (List Expr) := do
  let mut out := []
  for i in [0:limit] do
    match ← replaceNth e pick i with
    | some m => out := out ++ [m]
    | none => break
  return out

def swapRelation (from_ to_ : Name) (cls : Name) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity from_ 4 then
    let args := e.getAppArgs
    let α := args[0]!
    try
      let u ← getLevel α
      let some v := u.dec | return none
      let inst ← synthInstance (mkApp (mkConst cls [v]) α)
      return some (mkAppN (mkConst to_ (e.getAppFn.constLevels!)) #[α, inst, args[2]!, args[3]!])
    catch _ => return none
  return none

def pickStrictness (e : Expr) : MetaM (Option Expr) := do
  if let some r ← swapRelation ``LT.lt ``LE.le ``LE e then return r
  if let some r ← swapRelation ``LE.le ``LT.lt ``LT e then return r
  return none

def pickConnective (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``And 2 then return some (mkAppN (mkConst ``Or) e.getAppArgs)
  if e.isAppOfArity ``Or 2 then return some (mkAppN (mkConst ``And) e.getAppArgs)
  return none

def pickQuantifier (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam n ty b bi => return some (.forallE n ty b bi)
    | _ => return none
  match e with
  | .forallE n ty b bi =>
    -- an object binder the body depends on; never a type, an instance, or a hypothesis arrow
    if b.hasLooseBVars && bi.isExplicit && !ty.isSort then
      if ← isProp (.forallE n ty b bi) then
        try return some (← mkAppM ``Exists #[Expr.lam n ty b bi]) catch _ => return none
    return none
  | _ => return none

def pickSwapArgs (e : Expr) : MetaM (Option Expr) := do
  for op in [``HSub.hSub, ``HDiv.hDiv] do
    if e.isAppOfArity op 6 then
      let args := e.getAppArgs
      if ← isDefEq args[0]! args[1]! then
        return some (mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, args[3]!, args[5]!, args[4]!])
  return none

def pickNumeral (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    match args[1]!.nat? with
    | some n =>
      let lit := mkRawNatLit (n + 1)
      try
        let u ← getLevel args[0]!
        let some v := u.dec | return none
        let inst ← synthInstance (mkAppN (mkConst ``OfNat [v]) #[args[0]!, lit])
        return some (mkAppN e.getAppFn #[args[0]!, lit, inst])
      catch _ => return none
    | none => return none
  return none

def pickers : List (String × (Expr → MetaM (Option Expr))) :=
  [("strictness", pickStrictness), ("connective", pickConnective), ("quantifier", pickQuantifier),
   ("swap-args", pickSwapArgs), ("numeral", pickNumeral)]

/-- Mutants of a proposition `body` under the binders in scope: the pickers,
then negation and dropped conjuncts. -/
def mutateBody (body : Expr) : MetaM (List (String × Expr)) := do
  let mut out : List (String × Expr) := []
  for (kind, pick) in pickers do
    for m in ← allMutants body pick do
      out := out ++ [(kind, m)]
  out := out ++ [("negate-conclusion", mkNot body)]
  if body.isAppOfArity ``And 2 then
    out := out ++ [("drop-conjunct", body.appFn!.appArg!), ("drop-conjunct", body.appArg!)]
  return out

def wellTyped (e : Expr) : MetaM Bool := do
  try Meta.check e; isProp e catch _ => pure false

/-- Whether cheap automation proves `original ↔ mutant`. One-sided: a success
marks the mutant as equivalent, so a judge that passes it is right, not blind;
a failure proves nothing. The sweep is the probes' sweep plus a split of the
biconditional, and with Mathlib the symmetry of `|a - b|`, the equivalence the
first calibration run met most often. -/
def equivalent (original mutant : Expr) : TermElabM Bool := do
  let goal := mkApp2 (Lean.mkConst ``Iff) original mutant
  if (← AutoformProbe.attempt goal).isSome then return true
  for tac in [← `(tactic| (intros; constructor <;> intro h <;> simp_all)), {equivalence_tactics}] do
    let saved ← saveState
    let ok ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => {{ ctx with maxHeartbeats := AutoformProbe.budget }}) <| Core.withCurrHeartbeats do
        withLCtx {{}} {{}} do
          let mvar ← mkFreshExprMVar goal
          Term.runTactic mvar.mvarId! tac .term
          let value ← instantiateMVars mvar
          pure (!value.hasExprMVar && !value.hasSorry))
      (fun _ => pure false)
    restoreState saved
    if ok then return true
  return false

/-- Mutants of a theorem statement, printed. Hypothesis drops are made at the
telescope; everything else in the body. -/
def theoremMutants (type : Expr) : TermElabM (Array Json) := do
  let mut out : Array Json := #[]
  let full ← forallTelescope type fun fvars body => do
    let mut ms : List (String × Expr) := []
    for fv in fvars do
      if ← isProp (← inferType fv) then
        let keep := fvars.filter (· != fv)
        let g ← mkForallFVars keep body
        unless g.hasAnyFVar (· == fv.fvarId!) do
          ms := ms ++ [("drop-hypothesis", g)]
    for (kind, m) in ← mutateBody body do
      ms := ms ++ [(kind, ← mkForallFVars fvars m)]
    return ms
  for (kind, m) in full do
    if m == type then continue
    if ← wellTyped m then
      out := out.push <| Json.mkObj [("kind", Json.str kind), ("statement", Json.str (toString (← ppExpr m))),
        ("equivalent", Json.bool (← equivalent type m))]
  return out

/-- Mutants of a propositional definition's body, printed as `binders := body`,
plus the hollow definition `True`. -/
def definitionMutants (root : Name) (value : Expr) : TermElabM (Array Json) := do
  lambdaTelescope value fun fvars body => do
    unless ← isProp body do return #[]
    let binders ← fvars.mapM fun fv => do
      let decl ← fv.fvarId!.getDecl
      return s!"({{decl.userName}} : {{← ppExpr decl.type}})"
    let head := s!"{{root}} {{" ".intercalate binders.toList}} : Prop :="
    let mut out : Array Json := #[]
    let candidates := (← mutateBody body) ++ [("hollow", Lean.mkConst ``True)]
    for (kind, m) in candidates do
      if m == body then continue
      if ← wellTyped m then
        let same ← equivalent (← mkForallFVars fvars body) (← mkForallFVars fvars m)
        out := out.push <| Json.mkObj [("kind", Json.str kind), ("statement", Json.str s!"{{head}} {{← ppExpr m}}"),
          ("equivalent", Json.bool same)]
    return out

/-- The original in the same printed form the mutants use, so packets are uniform. -/
def printedOriginal (root : Name) : TermElabM String := do
  let some info := (← getEnv).find? root | return ""
  match info with
  | .defnInfo v =>
    lambdaTelescope v.value fun fvars body => do
      unless ← isProp body do return toString (← ppExpr info.type)
      let binders ← fvars.mapM fun fv => do
        let decl ← fv.fvarId!.getDecl
        return s!"({{decl.userName}} : {{← ppExpr decl.type}})"
      return s!"{{root}} {{" ".intercalate binders.toList}} : Prop := {{← ppExpr body}}"
  | _ => return toString (← ppExpr info.type)

def report (root : Name) : CommandElabM (List (String × Json)) := do
  let some info := (← getEnv).find? root | return []
  let mutants ← match info with
    | .defnInfo v => liftTermElabM (definitionMutants root v.value)
    | .thmInfo _ | .axiomInfo _ => liftTermElabM (theoremMutants info.type)
    | _ => pure #[]
  let original ← liftTermElabM (printedOriginal root)
  return [("mutants", Json.arr mutants), ("printed", Json.str original)]

end AutoformMutate

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
      ((l.toSubstring.drop 5).toString.splitOn " ")
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
    return some ((snippet.extract 0 pos).trimAsciiEnd.toString)

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
  let extra ← if {probe_enabled} then AutoformProbe.report root else pure []
  let extra := extra ++ (← if {mutate_enabled} then AutoformMutate.report root else pure [])
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
    ("axioms", Json.arr ((axioms.qsort Name.lt).map fun d => Json.str (toString d)))] ++ extra

end AutoformSkeleton

set_option maxHeartbeats 0 in
run_cmd do
  let projectRoots : List Name := [{project_roots}]
  for root in [{roots}] do
    AutoformSkeleton.skeleton projectRoots root
