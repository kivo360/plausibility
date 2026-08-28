/-
Semantics of propositional formulas: the set of truth assignments satisfying a
formula, satisfiability, and the logical (counting) probability of `A` given
`X`.  This is the semantic layer of the Lean formalization of Kevin S. Van
Horn, *From propositional logic to plausible reasoning: A uniqueness theorem*,
IJAR 88 (2017) 309–332.

For a finite atom type `α`, `models φ` is the finite set of all truth
assignments `v : α → Bool` with `φ.eval v = true`.  The logical probability of
`A` given `X` is the ratio of the number of assignments satisfying both to the
number satisfying `X`.
-/

import Plausibility.PropLogic.Formula

namespace Plausibility

variable {α : Type*}

/-- The set of truth assignments `v : α → Bool` satisfying `φ` — the finite
model set `M(φ)` of the paper.

New to Mathlib?  Read the body as set-builder notation over a finite universe:
`Finset.univ` is *every* valuation (the type `α → Bool` is itself finite, i.e.
the full truth table), and `.filter (fun v => φ.eval v = true)` keeps exactly
the satisfying ones — `{v | φ.eval v = true}`.  These are two independent
definitions (`Mathlib/Data/Fintype/Defs.lean` and
`Mathlib/Data/Finset/Filter.lean`), composed by dot notation.  See
`READING.md` in the repo root.  The predicate is decidable (equality on
`Bool`), so this is computable. -/
def models [Fintype α] [DecidableEq α] (φ : Formula α) : Finset (α → Bool) :=
  Finset.univ.filter fun v => φ.eval v = true

theorem mem_models_iff [Fintype α] [DecidableEq α] {φ : Formula α} {v : α → Bool} :
    v ∈ models φ ↔ φ.eval v = true := by
  simp [models]

/-- A formula is satisfiable when some truth assignment satisfies it. -/
def Satisfiable [Fintype α] [DecidableEq α] (φ : Formula α) : Prop :=
  (models φ).Nonempty

theorem models_and_subset [Fintype α] [DecidableEq α] (A X : Formula α) :
    models (A.and X) ⊆ models X := by
  intro v hv
  rw [mem_models_iff] at hv ⊢
  simp [Formula.eval] at hv
  exact hv.2

theorem card_models_and_le [Fintype α] [DecidableEq α] (A X : Formula α) :
    (models (A.and X)).card ≤ (models X).card := by
  exact Finset.card_le_card (models_and_subset A X)

/-- The logical probability of `A` given `X`: the fraction of assignments
satisfying `X` that also satisfy `A`.  Requires `X` to be satisfiable so the
denominator is nonzero. -/
def logicalProbability [Fintype α] [DecidableEq α] (A X : Formula α)
    (_hX : Satisfiable X) : ℚ :=
  ((models (A.and X)).card : ℚ) / (models X).card

theorem logicalProbability_nonneg [Fintype α] [DecidableEq α] (A X : Formula α)
    (_hX : Satisfiable X) : 0 ≤ logicalProbability A X _hX := by
  unfold logicalProbability
  positivity

theorem logicalProbability_le_one [Fintype α] [DecidableEq α] (A X : Formula α)
    (hX : Satisfiable X) : logicalProbability A X hX ≤ 1 := by
  unfold logicalProbability
  have hcard : (models (A.and X)).card ≤ (models X).card := card_models_and_le A X
  have hpos : 0 < (models X).card := by
    exact Finset.card_pos.mpr hX
  have hden : (0 : ℚ) < (models X).card := by exact_mod_cast hpos
  have hnum : (0 : ℚ) ≤ (models (A.and X)).card := by positivity
  have hnumle : ((models (A.and X)).card : ℚ) ≤ (models X).card := by exact_mod_cast hcard
  exact (div_le_iff₀ hden).mpr (by nlinarith)

-- Concrete sanity checks over two atoms `Fin 2`, decided by exhaustive
-- enumeration.

namespace Sanity

open Formula

/-- Over two atoms, the tautology `a ∨ ¬a` is satisfied by all 4 assignments. -/
example : (models (atom (0 : Fin 2) |>.or (atom (0 : Fin 2) |>.neg))).card = 4 := by
  native_decide

/-- Over two atoms, `a ∧ b` is satisfied by exactly 1 assignment. -/
example : (models (atom (0 : Fin 2) |>.and (atom (1 : Fin 2)))).card = 1 := by
  native_decide

/-- Over two atoms, the contradiction `a ∧ ¬a` is satisfied by no assignment. -/
example : (models (atom (0 : Fin 2) |>.and (atom (0 : Fin 2) |>.neg))).card = 0 := by
  native_decide

/-- Over two atoms, `a → a` is a tautology: all 4 assignments satisfy it. -/
example : (models (atom (0 : Fin 2) |>.imp (atom (0 : Fin 2)))).card = 4 := by
  native_decide

end Sanity

end Plausibility
