/-
Basic definitions for the semantic (finite-world) layer of the Lean formalization of
Kevin S. Van Horn, *From propositional logic to plausible reasoning: A uniqueness
theorem*, International Journal of Approximate Reasoning 88 (2017) 309–332.

A plausibility system assigns to every event `A` (a finite set of worlds) inside a
finite, nonempty world space `Ω` a plausibility value `score A` in a partially
ordered type `P`, subject to the semantic analogues of Van Horn's Requirements:

* invariance under bijection of world spaces (semantic consequence of R1 + R2,
  cf. Definition 5 / Corollary 9 of the paper),
* invariance under adding irrelevant information as a product with an independent
  finite space (R3, cf. Lemma 10),
* strict increase along strict subset inclusion of events (R4, cf. Lemma 13).
-/

import Mathlib

universe u v

set_option linter.unusedSectionVars false

namespace Plausibility

variable {Ω Ω' Γ : Type u} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
  [Fintype Γ] [DecidableEq Γ]

/-- `EventEquiv A B`: the events `A` and `B`, possibly living in different world
spaces, are equivalent, meaning some bijection of world spaces carries `A` onto
`B`.  This is the semantic content of the paper's change-of-variables
transformations (Definition 5). -/
def EventEquiv (A : Finset Ω) (B : Finset Ω') : Prop :=
  ∃ e : Ω ≃ Ω', ∀ x, x ∈ A ↔ e x ∈ B

@[refl]
theorem EventEquiv.refl (A : Finset Ω) : EventEquiv A A :=
  ⟨Equiv.refl _, fun _ => Iff.rfl⟩

theorem EventEquiv.symm {A : Finset Ω} {B : Finset Ω'} (h : EventEquiv A B) :
    EventEquiv B A := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun x => ?_⟩
  have hx := he (e.symm x)
  rw [Equiv.apply_symm_apply] at hx
  exact hx.symm

theorem EventEquiv.trans {A : Finset Ω} {B : Finset Ω'} {C : Finset Γ}
    (h₁ : EventEquiv A B) (h₂ : EventEquiv B C) : EventEquiv A C := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨f, hf⟩ := h₂
  exact ⟨e.trans f, fun x => (he x).trans (hf (e x))⟩

/-- A plausibility system: Van Horn's plausibility function `(A | X)`, presented
in the semantic finite-world setting where the premise `X` has already been
converted into the world space `Ω := models X` of satisfying truth assignments
and the query `A` into the event of worlds satisfying it. -/
structure PlausibilitySystem (P : Type v) [PartialOrder P] where
  /-- The plausibility `score A` of the event `A` within the world space `Ω`. -/
  score : ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω], Finset Ω → P

  /-- Semantic consequence of R1 + R2 (change of variables, Corollary 9):
  plausibility is invariant under bijections of world spaces carrying events
  onto events. -/
  equiv_invariance :
    ∀ {Ω Ω' : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω'] (A : Finset Ω) (B : Finset Ω'),
      EventEquiv A B → score A = score B

  /-- R3 (irrelevant information, Lemma 10): taking the product of the world
  space with an independent finite space of possibilities does not change the
  plausibility of an event. -/
  irrelevant_product :
    ∀ {Ω Γ : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] (A : Finset Ω),
      score A = score (A ×ˢ (Finset.univ : Finset Γ))

  /-- R4 (preservation of the implication ordering): an event that is a strict
  subset of another is strictly less plausible. -/
  strict_mono :
    ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] {A B : Finset Ω},
      A ⊂ B → score A < score B

end Plausibility
