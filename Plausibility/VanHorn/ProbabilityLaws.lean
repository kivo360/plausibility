/-
Probability laws for the logical (counting) probability measure over a finite
atom type `α`.  This formalizes Corollary 15 of Kevin S. Van Horn, *From
propositional logic to plausible reasoning: A uniqueness theorem*, IJAR 88
(2017) 309–332, for the counting measure: complementation
(`probability_complement`) and the product rule for conjunction
(`probability_conjunction`), together with the Finset cardinality law they
rest on (`card_models_neg_and`).
-/

import Plausibility.PropLogic.Semantics
import Mathlib.Tactic

namespace Plausibility

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The assignments satisfying `X` split into those satisfying `A` and those
satisfying `¬A`, so the corresponding model counts add up to the count for
`X`.  This is Corollary 15's additivity law, for the counting measure. -/
theorem card_models_neg_and (A X : Formula α) :
    (models ((A.neg).and X)).card + (models (A.and X)).card = (models X).card := by
  have hdisj : Disjoint (models (A.and X)) (models ((A.neg).and X)) := by
    rw [Finset.disjoint_left]
    intro v hvA hvN
    rw [mem_models_iff] at hvA hvN
    simp [Formula.eval] at hvA hvN
    have hAtrue : A.eval v = true := hvA.1
    have hAfalse : A.eval v = false := hvN.1
    rw [hAfalse] at hAtrue
    simp at hAtrue
  have hcover : models (A.and X) ∪ models ((A.neg).and X) = models X := by
    apply Finset.ext
    intro v
    rw [Finset.mem_union]
    by_cases hA : A.eval v = true
    · simp [mem_models_iff, Formula.eval, hA]
    · have hA' : A.eval v = false := Bool.eq_false_iff.mpr (by simp [hA])
      simp [mem_models_iff, Formula.eval, hA]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hcover] at hcard
  omega

/-- Complement law for the logical probability: `P(¬A | X) = 1 - P(A | X)`. -/
theorem probability_complement (A X : Formula α) (hX : Satisfiable X) :
    logicalProbability (A.neg) X hX = 1 - logicalProbability A X hX := by
  unfold logicalProbability
  have hpos : (0 : ℚ) < (models X).card := by
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hnum : ((models ((A.neg).and X)).card : ℚ) + (models (A.and X)).card = (models X).card := by
    exact_mod_cast card_models_neg_and A X
  field_simp [hpos]
  nlinarith

/-- `(A ∧ B) ∧ X` and `A ∧ (B ∧ X)` are satisfied by the same assignments. -/
theorem models_and_and_assoc (A B X : Formula α) :
    models ((A.and B).and X) = models (A.and (B.and X)) := by
  apply Finset.ext
  intro v
  simp [mem_models_iff, Formula.eval, and_assoc]

/-- Product rule for conjunction:
`P(A ∧ B | X) = P(B | X) * P(A | B ∧ X)`. -/
theorem probability_conjunction {A B X : Formula α} (hX : Satisfiable X)
    (hBX : Satisfiable (B.and X)) :
    logicalProbability (A.and B) X hX = logicalProbability B X hX * logicalProbability A (B.and X) hBX := by
  unfold logicalProbability
  have hposX : (0 : ℚ) < (models X).card := by
    exact_mod_cast (Finset.card_pos.mpr hX)
  have hposBX : (0 : ℚ) < (models (B.and X)).card := by
    exact_mod_cast (Finset.card_pos.mpr hBX)
  have hassoc : models ((A.and B).and X) = models (A.and (B.and X)) := models_and_and_assoc A B X
  field_simp [hposX, hposBX]
  rw [hassoc]

/-- The logical probability extended to unsatisfiable conditions by returning
`1`, kept separate from the core (unconditional) definition. -/
noncomputable def extendedProbability (A X : Formula α) : ℚ := by
  classical
  exact if h : Satisfiable X then logicalProbability A X h else 1

/-- On a satisfiable condition, the extended probability agrees with the
core logical probability. -/
theorem extendedProbability_eq_of_satisfiable (A X : Formula α) (hX : Satisfiable X) :
    extendedProbability A X = logicalProbability A X hX := by
  simp [extendedProbability, hX]

end Plausibility
