/-
The canonical problem `Υ₂(m, n)` of Van Horn (Lemma 6 / Corollary 8): a world
space of `n` possible cases of which the first `m` are favorable.  We show every
event in every finite world space is equivalent (`EventEquiv`) to a canonical
event, so plausibility depends only on the pair `(m, n)` of favorable and total
case counts.

The canonical event lives in `ULift (Fin n)` so that it sits in the same
universe as the world spaces scored by the plausibility system under
consideration.
-/

import Plausibility.Basic

namespace Plausibility

universe u v

set_option linter.unusedSectionVars false

variable {P : Type v} [PartialOrder P] (sys : PlausibilitySystem P)

/-- The canonical event: the first `m` of `n` possible cases. -/
def canonicalEvent (m n : ℕ) : Finset (ULift.{u} (Fin n)) :=
  Finset.univ.filter fun i => i.down.val < m

theorem mem_canonicalEvent {m n : ℕ} {i : ULift (Fin n)} :
    i ∈ canonicalEvent m n ↔ i.down.val < m := by
  simp [canonicalEvent]

theorem canonicalEvent_card {m n : ℕ} (hmn : m ≤ n) : (canonicalEvent m n).card = m := by
  classical
  have e : Fin m ≃ {i : ULift (Fin n) // i ∈ canonicalEvent m n} :=
    ⟨fun i => ⟨ULift.up ⟨i.val, Nat.lt_of_lt_of_le i.2 hmn⟩, mem_canonicalEvent.2 i.2⟩,
     fun i => ⟨i.1.down.val, mem_canonicalEvent.1 i.2⟩,
     fun i => Fin.ext (by simp [mem_canonicalEvent]),
     fun i => by ext; simp [mem_canonicalEvent]⟩
  rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_fin]

namespace PlausibilitySystem

variable {P : Type v} [PartialOrder P] (sys : PlausibilitySystem P)

/-- The plausibility of the canonical problem with `n` possible cases of which
`m` are favorable: `score` of the canonical event (Corollary 8). -/
def upsilon₂ (m n : ℕ) (hn : 0 < n) (hmn : m ≤ n) : P :=
  haveI : Nonempty (ULift (Fin n)) := ⟨ULift.up ⟨0, hn⟩⟩
  sys.score (canonicalEvent m n)

end PlausibilitySystem

section CanonicalEquiv

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem card_le_card {A : Finset Ω} : A.card ≤ Fintype.card Ω :=
  (Finset.card_le_univ A).trans_eq Finset.card_univ

/-- **Lemma 6 (semantic half)**. Every event in a finite, nonempty world space
is equivalent to a canonical event: there is a bijection of world spaces sending
`A` onto the first `A.card` of `Fintype.card Ω` elements. -/
theorem eventEquiv_canonical (A : Finset Ω) :
    EventEquiv A (canonicalEvent A.card (Fintype.card Ω)) := by
  classical
  -- equivalences of the two parts
  have eA : ↥A ≃ Fin A.card := Fintype.equivFinOfCardEq (Fintype.card_coe A)
  have eC : {x // x ∉ A} ≃ Fin (Fintype.card Ω - A.card) := by
    apply Fintype.equivFinOfCardEq
    have h1 : Fintype.card {x // x ∉ A} = Fintype.card ↥(Aᶜ : Finset Ω) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Finset.mem_compl.symm))
    rw [h1, Fintype.card_coe, Finset.card_compl]
  -- the composite world-space bijection
  set E : Ω ≃ ULift.{u} (Fin (Fintype.card Ω)) :=
    ((Equiv.sumCompl (fun x => x ∈ A)).symm.trans (eA.sumCongr eC)).trans
      (finSumFinEquiv.trans ((finCongr (by have h2 := card_le_card (A := A); omega)).trans Equiv.ulift.symm))
    with hE
  refine ⟨E, fun x => ?_⟩
  by_cases hx : x ∈ A
  · have hpos : (Equiv.sumCompl (fun x => x ∈ A)).symm x = Sum.inl ⟨x, hx⟩ :=
      Equiv.sumCompl_symm_apply_of_pos hx
    have h1 : (eA ⟨x, hx⟩).val < A.card := (eA ⟨x, hx⟩).2
    simp only [mem_canonicalEvent, Equiv.trans_apply, Equiv.ulift_symm_down,
      Equiv.sumCongr_apply, hE, Equiv.trans_apply, hpos, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.val_castAdd,
      Equiv.trans_apply, Equiv.trans_apply, ULift.down_up, finCongr_apply_coe, hx, true_iff]
    omega
  · have hneg : (Equiv.sumCompl (fun x => x ∈ A)).symm x = Sum.inr ⟨x, hx⟩ :=
      Equiv.sumCompl_symm_apply_of_neg hx
    have h1 : (eC ⟨x, hx⟩).val < Fintype.card Ω - A.card := (eC ⟨x, hx⟩).2
    have h2 : A.card ≤ Fintype.card Ω := card_le_card
    simp only [mem_canonicalEvent, Equiv.trans_apply, Equiv.ulift_symm_down,
      Equiv.sumCongr_apply, hE, Equiv.trans_apply, hneg, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right,
      Equiv.trans_apply, Equiv.trans_apply, ULift.down_up, finCongr_apply_coe,
      Fin.val_natAdd, hx, false_iff]
    omega

end CanonicalEquiv

/-- **Corollary 8**. Plausibility depends only on the pair `(m, n)` of
favorable and total case counts: every event scores exactly like its canonical
form. -/
theorem score_eq_canonical {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : Finset Ω) :
    sys.score A =
      sys.upsilon₂ A.card (Fintype.card Ω) Fintype.card_pos card_le_card := by
  simp only [PlausibilitySystem.upsilon₂]
  exact sys.equiv_invariance A _ (eventEquiv_canonical A)

end Plausibility
