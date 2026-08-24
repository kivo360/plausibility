/-
Propositional formulas over an arbitrary set of atoms `α`, together with a
Boolean evaluation.  This is the syntactic layer of the Lean formalization of
Kevin S. Van Horn, *From propositional logic to plausible reasoning: A
uniqueness theorem*, IJAR 88 (2017) 309–332.

The primitive connectives are `atom`, `bot` (falsum), `neg`, and `and`; the
remaining classical connectives (`top`, `or`, `imp`, `iff`) are derived
definitions.  We use the bare names `top`, `or`, `imp`, `iff` inside the
`Plausibility` namespace; they do not collide with Mathlib names because they
are scoped to this namespace and are not notation.
-/

import Mathlib

namespace Plausibility

/-- Propositional formulas over atoms `α`. -/
inductive Formula (α : Type*) where
  | atom : α → Formula α
  | bot : Formula α
  | neg : Formula α → Formula α
  | and : Formula α → Formula α → Formula α

namespace Formula

/-- The constant true formula `⊤`. -/
def top : Formula α := neg bot

/-- Disjunction `φ ∨ ψ`, derived as `¬(¬φ ∧ ¬ψ)`. -/
def or (φ ψ : Formula α) : Formula α := neg (and (neg φ) (neg ψ))

/-- Implication `φ → ψ`, derived as `¬(φ ∧ ¬ψ)`. -/
def imp (φ ψ : Formula α) : Formula α := neg (and φ (neg ψ))

/-- Biconditional `φ ↔ ψ`, derived as `(φ → ψ) ∧ (ψ → φ)`. -/
def iff (φ ψ : Formula α) : Formula α := and (imp φ ψ) (imp ψ φ)

/-- Boolean evaluation of a formula under a truth assignment `v : α → Bool`. -/
def eval (v : α → Bool) : Formula α → Bool
  | atom a => v a
  | bot => false
  | neg φ => !eval v φ
  | and φ ψ => eval v φ && eval v ψ

end Formula

end Plausibility
