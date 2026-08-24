/-
Van Horn's four Requirements, stated syntactically over the single global
(countably infinite) atom language `Atom := ℕ`, exactly as the paper does:
one plausibility function on query–premise pairs for all problem domains.

Semantic notions here are evaluation-based (no finiteness): `X ≡ Y` means the
formulas evaluate identically under every valuation; `X ⊨ A` is pointwise
entailment; satisfiability is existential.  Finiteness enters only when
*counting* models, via `Plausibility.modelsOn` over finite atom supports.

R2 is stated with explicit freshness (`s` outside the supports); R3 requires
the irrelevant formula's vocabulary to be disjoint.  The remaining gap for the
full syntactic bridge is Lemma 6 (see `Reduction.lean`): from `r1` and `r2`,
`value A X` depends only on the model counts of `A ∧ X` and `X`.
-/

import Plausibility.VanHorn.Substitution

namespace Plausibility

universe v

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The global propositional language: one countably infinite symbol set,
as in the paper. -/
abbrev Atom : Type := ℕ

namespace Formula

variable {X Y Z A B : Formula Atom} {v : Atom → Bool}

/-- Logical equivalence: same truth value under every valuation. -/
def Eqv (X Y : Formula Atom) : Prop := ∀ v, X.eval v = Y.eval v

/-- Equivalence of queries *assuming* a premise. -/
def EqvAt (X A B : Formula Atom) : Prop :=
  ∀ v, X.eval v = true → A.eval v = B.eval v

/-- Semantic entailment. -/
def Entails (X A : Formula Atom) : Prop := ∀ v, X.eval v = true → A.eval v = true

/-- Satisfiability. -/
def Sat (φ : Formula Atom) : Prop := ∃ v, φ.eval v = true

@[refl] theorem Eqv.refl (X : Formula Atom) : X.Eqv X := fun _ => rfl

theorem Eqv.symm (h : X.Eqv Y) : Y.Eqv X := fun v => (h v).symm

theorem Eqv.trans (h₁ : X.Eqv Y) (h₂ : Y.Eqv Z) : X.Eqv Z := fun v => (h₁ v).trans (h₂ v)

theorem Sat.entails_of_eqv (hX : X.Sat) (h : X.Eqv Y) : Y.Sat := by
  obtain ⟨v, hv⟩ := hX
  exact ⟨v, by rw [← h v, hv]⟩

end Formula

open Formula

/-- A plausibility function on propositional query–premise pairs over the
global language, subject to Van Horn's four Requirements. -/
structure LogicalPlausibility (P : Type v) [PartialOrder P] where
  /-- The plausibility `(A | X)` of query `A` given premise `X`. -/
  value : Formula Atom → Formula Atom → P

  /-- **R1.** If `X ≡ Y` and `A ≡ₓ B`, then `(A | X) = (B | Y)`. -/
  r1 : ∀ {A B X Y : Formula Atom},
    X.Eqv Y → X.EqvAt A B → value A X = value B Y

  /-- **R2.** Defining a fresh symbol `s ∉ σ(A, X, E)` as `E` does not change
  plausibility.  (As an equation it applies in both directions: adding and
  removing a definition.) -/
  r2 : ∀ (s : Atom) (A X E : Formula Atom),
    s ∉ A.support ∪ X.support ∪ E.support →
      value A ((Formula.atom s).iff E |>.and X) = value A X

  /-- **R3.** Adding a satisfiable premise `Y` over a disjoint vocabulary does
  not change plausibility. -/
  r3 : ∀ (A X Y : Formula Atom), Y.Sat →
    Disjoint Y.support (A.support ∪ X.support) →
      value A (Y.and X) = value A X

  /-- **R4.** The implication ordering is preserved: if `X ⊨ A → B` but not
  `X ⊨ B → A`, then `(A | X) < (B | X)`. -/
  r4 : ∀ (A B X : Formula Atom),
    X.Entails (A.imp B) → ¬ X.Entails (B.imp A) → value A X < value B X

end Plausibility
