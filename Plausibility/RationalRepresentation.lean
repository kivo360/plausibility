/-
The rational representation `Υ₁` (Van Horn, Sections 6–7): plausibility of the
canonical problem depends only on the rational probability `m / n`, giving a
well-defined, strictly monotone map `upsilon₁ : Rat01 → P`.
-/

import Plausibility.ScaleInvariant

namespace Plausibility

universe u v

set_option linter.unusedSectionVars false

variable {P : Type v} [PartialOrder P] (sys : PlausibilitySystem P)

/-- Rational probabilities: `q ∈ ℚ ∩ [0, 1]`. -/
abbrev Rat01 : Type := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

/-- **Well-definedness of `Υ₁`.** If `m/n = m'/n'` as rational numbers, then
the canonical problems `(m, n)` and `(m', n')` have equal plausibility (both
scale to the common-denominator problem `(m n', n n')`). -/
theorem upsilon₂_eq_of_rat_eq (m n m' n' : ℕ) (hn : 0 < n) (hn' : 0 < n')
    (hmn : m ≤ n) (hmn' : m' ≤ n')
    (h : (m : ℚ) / n = (m' : ℚ) / n') :
    PlausibilitySystem.upsilon₂ sys m n hn hmn =
      PlausibilitySystem.upsilon₂ sys m' n' hn' hmn' := by
  have hcross : m * n' = m' * n := by
    have h1 := (div_eq_div_iff (by positivity) (by positivity)).mp h
    push_cast at h1
    exact_mod_cast h1
  have e1 := upsilon₂_scale sys m n n' hn hn' hmn
  have e2 := upsilon₂_scale sys m' n' n hn' hn hmn'
  simp only [PlausibilitySystem.upsilon₂] at e1 e2 ⊢
  have hc1 : n' * m = n * m' := by
    rw [Nat.mul_comm n' m, hcross, Nat.mul_comm m' n]
  have hc2 : n' * n = n * n' := Nat.mul_comm n' n
  rw [← e1, ← e2]
  haveI : Nonempty (ULift (Fin (n' * n))) := ⟨ULift.up ⟨0, Nat.mul_pos hn' hn⟩⟩
  haveI : Nonempty (ULift (Fin (n * n'))) := ⟨ULift.up ⟨0, Nat.mul_pos hn hn'⟩⟩
  exact sys.equiv_invariance _ _ ⟨Equiv.ulift.trans ((finCongr hc2).trans Equiv.ulift.symm),
    fun i => by
      simp only [mem_canonicalEvent, Equiv.trans_apply, Equiv.ulift_apply,
        Equiv.ulift_symm_down, Equiv.ulift_symm_apply, ULift.down_up, ULift.up_down,
        finCongr_apply_coe]
      omega⟩

theorem num_natAbs_le_den {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    q.num.natAbs ≤ q.den := by
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.2 h0
  have hd := (Rat.le_iff q 1).1 h1
  simp only [Rat.num_one, Rat.den_one, mul_one, Int.ofNat_eq_coe] at hd
  have hd' : q.num ≤ q.den := by simpa using hd
  omega

namespace PlausibilitySystem

open Plausibility (Rat01)

/-- `upsilon₁ q` — the plausibility of the rational probability `q`,
represented canonically by `q.num / q.den`; well-defined by
`upsilon₂_eq_of_rat_eq`. -/
noncomputable def upsilon₁ (sys : PlausibilitySystem P) (q : Rat01) : P :=
  upsilon₂ sys (q : ℚ).num.natAbs (q : ℚ).den (q : ℚ).den_pos
    (Plausibility.num_natAbs_le_den q.2.1 q.2.2)

theorem upsilon₁_eq_upsilon₂ (sys : PlausibilitySystem P) (m n : ℕ) (hn : 0 < n)
    (hmn : m ≤ n) :
    upsilon₁ sys ⟨(m : ℚ) / n,
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.2 hn)).2 (by exact_mod_cast hmn)⟩ =
      upsilon₂ sys m n hn hmn := by
  have h0 : 0 ≤ (m : ℚ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)
  have h1 : (m : ℚ) / n ≤ 1 :=
    (div_le_one (Nat.cast_pos.2 hn)).2 (by exact_mod_cast hmn)
  have hnum : (((m : ℚ) / n).num.natAbs : ℚ) = ((m : ℚ) / n).num := by
    simp [Int.natAbs_of_nonneg (Rat.num_nonneg.2 h0)] <;> assumption
  have hval : ((((m : ℚ) / n).num.natAbs : ℚ) / ((m : ℚ) / n).den) = (m : ℚ) / n := by
    rw [hnum, Rat.num_div_den]
  have h := Plausibility.upsilon₂_eq_of_rat_eq (P := P) sys m n ((m : ℚ) / n).num.natAbs
    ((m : ℚ) / n).den hn ((m : ℚ) / n).den_pos hmn
    (Plausibility.num_natAbs_le_den h0 h1) hval.symm
  exact h.symm

private theorem canonical_ssubset_witness {m n m' n' : ℕ} (hmn' : m' ≤ n')
    (h : m * n' < m' * n) : n' * m < n * m' ∧ n' * m < n * n' := by
  have c1 : n' * m = m * n' := Nat.mul_comm _ _
  have c2 : m' * n = n * m' := Nat.mul_comm _ _
  have h2 : n * m' ≤ n * n' := Nat.mul_le_mul_left _ hmn'
  exact ⟨by omega, by omega⟩

/-- **Lemma 13**. `upsilon₁` is strictly monotone: strictly larger rational
probability means strictly larger plausibility. -/
theorem upsilon₁_strictMono (sys : PlausibilitySystem P) :
    StrictMono (upsilon₁ (P := P) sys) := by
  intro a b hab
  have han0 : 0 ≤ (a : ℚ).num := Rat.num_nonneg.2 a.2.1
  have hbn0 : 0 ≤ (b : ℚ).num := Rat.num_nonneg.2 b.2.1
  have hanum : (((a : ℚ).num.natAbs : ℚ) = (a : ℚ).num) := by
    simp [Int.natAbs_of_nonneg han0, show (0:ℚ) ≤ a from a.2.1]
  have hbnum : (((b : ℚ).num.natAbs : ℚ) = (b : ℚ).num) := by
    simp [Int.natAbs_of_nonneg hbn0, show (0:ℚ) ≤ b from b.2.1]
  have haq : (a : ℚ) = (((a : ℚ).num.natAbs : ℚ) / (a : ℚ).den) := by
    rw [hanum, Rat.num_div_den]
  have hbq : (b : ℚ) = (((b : ℚ).num.natAbs : ℚ) / (b : ℚ).den) := by
    rw [hbnum, Rat.num_div_den]
  -- cross-multiplied strict inequality
  have hc : (a : ℚ).num.natAbs * (b : ℚ).den < (b : ℚ).num.natAbs * (a : ℚ).den := by
    have hlt : (((a : ℚ).num.natAbs : ℚ) / (a : ℚ).den <
        ((b : ℚ).num.natAbs : ℚ) / (b : ℚ).den) := by
      rw [← haq, ← hbq]; exact mod_cast hab
    have h1 := (div_lt_div_iff₀ (Nat.cast_pos.2 (a : ℚ).den_pos)
        (Nat.cast_pos.2 (b : ℚ).den_pos)).mp hlt
    push_cast at h1
    exact_mod_cast h1
  -- scale both to the common denominator (a.den * b.den)
  have hmna : (a : ℚ).num.natAbs ≤ (a : ℚ).den := Plausibility.num_natAbs_le_den a.2.1 a.2.2
  have hmnb : (b : ℚ).num.natAbs ≤ (b : ℚ).den := Plausibility.num_natAbs_le_den b.2.1 b.2.2
  have e1 := upsilon₂_scale sys (a : ℚ).num.natAbs (a : ℚ).den (b : ℚ).den
    (a : ℚ).den_pos (b : ℚ).den_pos hmna
  have e2 := upsilon₂_scale sys (b : ℚ).num.natAbs (b : ℚ).den (a : ℚ).den
    (b : ℚ).den_pos (a : ℚ).den_pos hmnb
  -- relabel the first scaled denominator to (a.den * b.den)
  have D1 : PlausibilitySystem.upsilon₂ sys ((b : ℚ).den * (a : ℚ).num.natAbs)
      ((b : ℚ).den * (a : ℚ).den) _ _ =
    PlausibilitySystem.upsilon₂ sys ((b : ℚ).den * (a : ℚ).num.natAbs)
      ((a : ℚ).den * (b : ℚ).den) _ _ :=
    upsilon₂_denom_eq sys _ _ _
      (Nat.mul_pos (b : ℚ).den_pos (a : ℚ).den_pos)
      (Nat.mul_pos (a : ℚ).den_pos (b : ℚ).den_pos)
      (Nat.mul_le_mul_left (b : ℚ).den hmna)
      (by
        have h1 : (b : ℚ).den * (a : ℚ).num.natAbs ≤ (b : ℚ).den * (a : ℚ).den :=
          Nat.mul_le_mul_left _ hmna
        have h2 : (b : ℚ).den * (a : ℚ).den = (a : ℚ).den * (b : ℚ).den := Nat.mul_comm _ _
        omega)
      (Nat.mul_comm _ _)
  -- strict subset of canonical events at the common denominator
  haveI : Nonempty (ULift (Fin ((a : ℚ).den * (b : ℚ).den))) :=
    ⟨ULift.up ⟨0, Nat.mul_pos (a : ℚ).den_pos (b : ℚ).den_pos⟩⟩
  have hcd : (b : ℚ).den * (a : ℚ).num.natAbs ≤ (a : ℚ).den * (b : ℚ).den := by
    have h1 : (b : ℚ).den * (a : ℚ).num.natAbs ≤ (b : ℚ).den * (a : ℚ).den :=
      Nat.mul_le_mul_left _ hmna
    have h2 : (b : ℚ).den * (a : ℚ).den = (a : ℚ).den * (b : ℚ).den := Nat.mul_comm _ _
    omega
  have key : PlausibilitySystem.upsilon₂ sys ((b : ℚ).den * (a : ℚ).num.natAbs)
      ((a : ℚ).den * (b : ℚ).den)
      (Nat.mul_pos (a : ℚ).den_pos (b : ℚ).den_pos) hcd <
    PlausibilitySystem.upsilon₂ sys ((a : ℚ).den * (b : ℚ).num.natAbs)
      ((a : ℚ).den * (b : ℚ).den)
      (Nat.mul_pos (a : ℚ).den_pos (b : ℚ).den_pos)
      (Nat.mul_le_mul_left (a : ℚ).den hmnb) := by
    refine sys.strict_mono ?_
    constructor
    · intro i hi
      simp only [mem_canonicalEvent] at hi ⊢
      have c1 : (b : ℚ).den * (a : ℚ).num.natAbs = (a : ℚ).num.natAbs * (b : ℚ).den :=
        Nat.mul_comm _ _
      have c2 : (a : ℚ).den * (b : ℚ).num.natAbs = (b : ℚ).num.natAbs * (a : ℚ).den :=
        Nat.mul_comm _ _
      omega
    · intro hEq
      -- boundary witness: strictly inside the larger event, on the boundary of the smaller
      have c1 : (b : ℚ).den * (a : ℚ).num.natAbs = (a : ℚ).num.natAbs * (b : ℚ).den :=
        Nat.mul_comm _ _
      have c2 : (a : ℚ).den * (b : ℚ).num.natAbs = (b : ℚ).num.natAbs * (a : ℚ).den :=
        Nat.mul_comm _ _
      have c3 : (b : ℚ).num.natAbs * (a : ℚ).den ≤ (b : ℚ).den * (a : ℚ).den :=
        Nat.mul_le_mul_right (a : ℚ).den hmnb
      obtain ⟨hw1, hw2⟩ :=
        canonical_ssubset_witness (m := (a : ℚ).num.natAbs) (n := (a : ℚ).den)
          (m' := (b : ℚ).num.natAbs) (n' := (b : ℚ).den) hmnb hc
      have hmem : (ULift.up ⟨(b : ℚ).den * (a : ℚ).num.natAbs, hw2⟩ :
          ULift (Fin ((a : ℚ).den * (b : ℚ).den))) ∈
          canonicalEvent ((a : ℚ).den * (b : ℚ).num.natAbs) ((a : ℚ).den * (b : ℚ).den) :=
        mem_canonicalEvent.2 (by
          have c2 : (a : ℚ).den * (b : ℚ).num.natAbs = (b : ℚ).num.natAbs * (a : ℚ).den :=
            Nat.mul_comm _ _
          omega)
      have hnot : (ULift.up ⟨(b : ℚ).den * (a : ℚ).num.natAbs, hw2⟩ :
          ULift (Fin ((a : ℚ).den * (b : ℚ).den))) ∉
          canonicalEvent ((b : ℚ).den * (a : ℚ).num.natAbs) ((a : ℚ).den * (b : ℚ).den) := by
        intro hcon
        simp only [mem_canonicalEvent, ULift.down_up, Fin.val_mk] at hcon
        exact Nat.lt_irrefl _ hcon
      exact hnot (hEq hmem)
  simp only [upsilon₁]
  calc PlausibilitySystem.upsilon₂ sys (a : ℚ).num.natAbs (a : ℚ).den _ _
      = PlausibilitySystem.upsilon₂ sys ((b : ℚ).den * (a : ℚ).num.natAbs)
          ((b : ℚ).den * (a : ℚ).den) _ _ := e1.symm
    _ = PlausibilitySystem.upsilon₂ sys ((b : ℚ).den * (a : ℚ).num.natAbs)
          ((a : ℚ).den * (b : ℚ).den) _ _ := D1
    _ < PlausibilitySystem.upsilon₂ sys ((a : ℚ).den * (b : ℚ).num.natAbs)
          ((a : ℚ).den * (b : ℚ).den) _ _ := key
    _ = PlausibilitySystem.upsilon₂ sys (b : ℚ).num.natAbs (b : ℚ).den _ _ := e2

end PlausibilitySystem

end Plausibility
