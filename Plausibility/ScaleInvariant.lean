/-
Scale invariance (Van Horn's Lemma 10, from R3): the canonical problems
`(m, n)` and `(k*m, k*n)` have equal plausibility, because adjoining `k`
irrelevant possibilities multiplies both the favorable and the total case
counts by `k` without changing the plausibility.
-/

import Plausibility.Canonical

namespace Plausibility

universe u v

set_option linter.unusedSectionVars false

variable {P : Type v} [PartialOrder P] (sys : PlausibilitySystem P)

/-- The product event `canonicalEvent m n ×ˢ univ` in the world space
`ULift (Fin n) × ULift (Fin k)` is equivalent to the canonical event with
`(k*m, k*n)` cases. -/
theorem eventEquiv_prod_canonical (m n k : ℕ) (hk : 0 < k) (hmn : m ≤ n) :
    EventEquiv
      ((canonicalEvent m n ×ˢ Finset.univ :
        Finset (ULift.{u} (Fin n) × ULift.{u} (Fin k))))
      (canonicalEvent (k * m) (k * n)) := by
  set e : ULift.{u} (Fin n) × ULift.{u} (Fin k) ≃ ULift.{u} (Fin (k * n)) :=
    (Equiv.prodCongr Equiv.ulift Equiv.ulift).trans
      (finProdFinEquiv.trans ((finCongr (Nat.mul_comm n k)).trans Equiv.ulift.symm))
    with he
  refine ⟨e, fun p => ?_⟩
  have hj : p.2.down.val < k := p.2.down.2
  have hin : p.1.down.val < n := p.1.down.2
  have hval : (e p).down.val = p.2.down.val + k * p.1.down.val := by
    simp [he, Equiv.prodCongr_apply, Equiv.ulift, Equiv.ulift_symm_down, finCongr]
  rw [Finset.mem_product, mem_canonicalEvent, mem_canonicalEvent, hval]
  constructor
  · intro h
    have h1 : (p.1.down.val + 1) * k ≤ m * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt h.1)
    have h2 : (p.1.down.val + 1) * k = p.1.down.val * k + k := Nat.succ_mul _ _
    have h3 : m * k = k * m := Nat.mul_comm m k
    have h4 : p.1.down.val * k = k * p.1.down.val := Nat.mul_comm _ _
    omega
  · intro h
    have e1 : k * m = m * k := Nat.mul_comm k m
    have e2 : p.1.down.val * k = k * p.1.down.val := Nat.mul_comm _ _
    have hlt : p.1.down.val * k < m * k := by omega
    exact ⟨Nat.lt_of_mul_lt_mul_right hlt, Finset.mem_univ _⟩

/-- **Lemma 10** (scale invariance). For `k > 0`, the canonical problems
`(m, n)` and `(k*m, k*n)` have the same plausibility: plausibility depends only
on the ratio `m / n`. -/
theorem upsilon₂_scale (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hmn : m ≤ n) :
    PlausibilitySystem.upsilon₂ sys (k * m) (k * n) (Nat.mul_pos hk hn)
        (Nat.mul_le_mul_left k hmn) =
      PlausibilitySystem.upsilon₂ sys m n hn hmn := by
  haveI : Nonempty (ULift (Fin n)) := ⟨ULift.up ⟨0, hn⟩⟩
  haveI : Nonempty (ULift (Fin k)) := ⟨ULift.up ⟨0, hk⟩⟩
  haveI : Nonempty (ULift (Fin (k * n))) := ⟨ULift.up ⟨0, Nat.mul_pos hk hn⟩⟩
  have h1 : sys.score (canonicalEvent (k * m) (k * n)) =
      sys.score (canonicalEvent m n ×ˢ (Finset.univ : Finset (ULift (Fin k)))) :=
    sys.equiv_invariance _ _ (eventEquiv_prod_canonical m n k hk hmn).symm
  have h2 : sys.score (canonicalEvent m n) =
      sys.score (canonicalEvent m n ×ˢ (Finset.univ : Finset (ULift (Fin k)))) :=
    sys.irrelevant_product _
  simp only [PlausibilitySystem.upsilon₂]
  rw [h1, h2]

/-- Transport along equality of the case counts: `upsilon₂` only depends on
the values of `m` and `n`, not on how they are presented. -/
theorem upsilon₂_denom_eq (m n n' : ℕ) (hn : 0 < n) (hn' : 0 < n')
    (hmn : m ≤ n) (hmn' : m ≤ n') (hnn : n = n') :
    PlausibilitySystem.upsilon₂ sys m n hn hmn =
      PlausibilitySystem.upsilon₂ sys m n' hn' hmn' := by
  subst hnn
  rfl

end Plausibility
