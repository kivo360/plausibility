/-
Van Horn's four Requirements, stated syntactically on a plausibility function
taking propositional query–premise pairs, over atom types of all finite sizes.

This is the interface the full propositional bridge (Lemma 6 / Corollary 9)
must target: from a `LogicalPlausibility` satisfying R1–R4 one must derive the
semantic `PlausibilitySystem` axioms, after which the representation theorem
(Theorem 14) applies verbatim.  The derivation itself (fresh-symbol iteration,
change of variables, canonical reduction) is future work; the semantic
ingredients already proved are `Plausibility.r2Equiv` (definitions do not
change model counts) and `Plausibility.sumEquiv` (disjoint vocabularies
split model counts as a product).
-/

import Plausibility.VanHorn.Substitution
import Plausibility.PropLogic.Semantics

namespace Plausibility

universe u v

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {α β : Type u} [Fintype α] [DecidableEq α]

/-- Logical equivalence of premises (same models). -/
def Formula.Eqv (X Y : Formula α) : Prop := models X = models Y

/-- Logical equivalence of queries *assuming* a premise: `A` and `B` have the
same models among the models of `X`. -/
def Formula.EqvAt (X A B : Formula α) : Prop :=
  models (A.and X) = models (B.and X)

/-- Semantic entailment. -/
def Formula.Entails (X A : Formula α) : Prop := models X ⊆ models A

/-- A plausibility function on propositional query–premise pairs, subject to
Van Horn's four Requirements.  Values live in a partial order; the world of
atom types covers every finite vocabulary. -/
structure LogicalPlausibility (P : Type v) [PartialOrder P] where
  /-- The plausibility `(A | X)` of query `A` given premise `X`. -/
  value : ∀ {α : Type u} [Fintype α] [DecidableEq α], Formula α → Formula α → P

  /-- **R1.** If `X ≡ Y` and `A ≡ₓ B`, then `(A | X) = (B | Y)`. -/
  r1 : ∀ {α : Type u} [Fintype α] [DecidableEq α] (A B X Y : Formula α),
    X.Eqv Y → X.EqvAt A B → value A X = value B Y

  /-- **R2.** Defining a fresh symbol `s` (not occurring in `A`, `X`, `E`) as
  `E` does not change plausibility:
  `(lift A | (s ↔ lift E) ∧ lift X) = (A | X)`. -/
  r2 : ∀ {α : Type u} [Fintype α] [DecidableEq α] (A X E : Formula α),
    value (A.mapLift some) ((defFormula E).and (X.mapLift some)) = value A X

  /-- **R3.** Adding a satisfiable premise `Y` over a disjoint vocabulary does
  not change plausibility. -/
  r3 : ∀ {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (A X : Formula α) (Y : Formula β), Satisfiable Y →
    value (A.mapLift Sum.inl)
      ((X.mapLift Sum.inl).and (Y.mapLift Sum.inr)) = value A X

  /-- **R4.** The implication ordering is preserved: if `X ⊨ A → B` but not
  `X ⊨ B → A`, then `(A | X) < (B | X)`. -/
  r4 : ∀ {α : Type u} [Fintype α] [DecidableEq α] (A B X : Formula α),
    X.Entails (A.imp B) → ¬ X.Entails (B.imp A) → value A X < value B X

end Plausibility
