namespace Skel

variable {Y : Type}

/-- A weak observation admits a label. -/
def Eligible (S : Y → Prop) (y : Y) : Prop := S y

/-- At most one label is admitted. -/
def NonAmbiguous (S : Y → Prop) : Prop :=
  ∀ y z : Y, Eligible S y → Eligible S z → y = z

/-- A helper only used inside a proof; must NOT appear in a skeleton. -/
theorem eligible_of (S : Y → Prop) (y : Y) (h : S y) : Eligible S y := h

/-- A structure, to check inductive handling. -/
structure Observation (Y : Type) where
  admits : Y → Prop
  nonempty : ∃ y, admits y

/-- A class, to check that a local class projection folds onto the class. -/
class HasWeight (Y : Type) where
  weight : Y → Nat

/-- Uses the class projection in its body. -/
def heavy [HasWeight Y] (y : Y) : Prop := 0 < HasWeight.weight y

/-- Scoped notation: only parses where `Skel` is open. -/
scoped notation "⟪" y "⟫" => HasWeight.weight y

/-- Holds of everything: a vacuous definition the checks must flag. -/
def Always (y : Y) : Prop := y = y

/-- Ignores its argument and holds of nothing. -/
def Ignores (y : Y) : Prop := False

/-- The second clause follows from the first. -/
def Redundant (S : Y → Prop) (y : Y) : Prop := Eligible S y ∧ S y

theorem NonAmbiguous.witness : NonAmbiguous (fun z : Nat => z = 0) := fun y z hy hz => hy.trans hz.symm
theorem NonAmbiguous.counterexample : ¬ NonAmbiguous (fun _ : Nat => True) :=
  fun h => absurd (h 0 1 trivial trivial) (by decide)
/-- Filed as a counterexample but has the wrong shape. -/
theorem Always.counterexample : Always (1 : Nat) := rfl

end Skel
