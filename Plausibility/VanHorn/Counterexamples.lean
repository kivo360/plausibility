import Plausibility.ProbabilityTheorem

namespace Plausibility

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

/-- The three-valued truth lattice: `falseV`, `unknownV`, `trueV`. -/
inductive ThreeVal | falseV | unknownV | trueV

namespace ThreeVal

/-- A rank function witnessing `ThreeVal`'s linear order:
`falseV < unknownV < trueV`. -/
def rank : ThreeVal → ℕ
  | .falseV => 0
  | .unknownV => 1
  | .trueV => 2

end ThreeVal

instance : PartialOrder ThreeVal :=
  PartialOrder.lift ThreeVal.rank (by
    intro a b h
    cases a <;> cases b <;> simp [ThreeVal.rank] at h ⊢)

namespace threeSystem

/-- A three-valued plausibility score: `falseV` on the empty event, `trueV` on
the whole world space, and `unknownV` on any genuinely intermediate event.

This satisfies R1+R2 (equivariance) and R3 (irrelevant product), but *violates*
R4 (strict monotonicity): two nested intermediate events both score
`unknownV`.  Consequently this score does **not** extend to a
`PlausibilitySystem` (whose `strict_mono` field would be unprovable), so we
present it here as a standalone score together with the two properties that
*do* hold. -/
noncomputable def score {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (A : Finset Ω) : ThreeVal :=
  if A = ∅ then .falseV else if A = Finset.univ then .trueV else .unknownV

/-- R1+R2 (change of variables): `threeSystem` is invariant under bijections of
world spaces carrying events onto events. -/
theorem equiv_invariance {Ω Ω' : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω'] (A : Finset Ω) (B : Finset Ω')
    (h : EventEquiv A B) : score A = score B := by
  obtain ⟨e, he⟩ := h
  have hcard : A.card = B.card := by
    have se : ↥A ≃ ↥B :=
      Equiv.ofBijective (fun x => ⟨e x, (he x.1).1 x.2⟩)
        ⟨fun x y hxy => Subtype.ext (e.injective (Subtype.ext_iff.1 hxy)), fun y => by
          refine ⟨⟨e.symm y, ?_⟩, ?_⟩
          · exact (he (e.symm y.1)).2 (by
              rw [Equiv.apply_symm_apply]; exact y.2)
          · apply Subtype.ext
            simp [Equiv.apply_symm_apply]⟩
    rw [← Fintype.card_coe, ← Fintype.card_coe, Fintype.card_congr se]
  have hΩ : Fintype.card Ω = Fintype.card Ω' := Fintype.card_congr e
  by_cases hA : A = ∅
  · have hB : B = ∅ := by
      apply Finset.card_eq_zero.mp
      calc B.card = A.card := hcard.symm
        _ = 0 := by simp [hA]
    simp [score, hA, hB]
  · by_cases hU : A = Finset.univ
    · have hB : B = Finset.univ := by
        apply (Finset.card_eq_iff_eq_univ B).mp
        calc B.card = A.card := hcard.symm
          _ = Fintype.card Ω := by simp [hU, Finset.card_univ]
          _ = Fintype.card Ω' := hΩ
      rw [hU, hB]
      have hAe : (Finset.univ : Finset Ω) ≠ ∅ := by
        intro h
        exact (Finset.ne_empty_of_mem (Finset.mem_univ (Classical.arbitrary Ω))) h
      have hBe : (Finset.univ : Finset Ω') ≠ ∅ := by
        intro h
        exact (Finset.ne_empty_of_mem (Finset.mem_univ (Classical.arbitrary Ω'))) h
      simp [score, hAe, hBe]
    · have hBne : B ≠ ∅ := by
        intro hB
        apply hA
        apply Finset.card_eq_zero.mp
        calc A.card = B.card := hcard
          _ = 0 := by simp [hB]
      have hBu : B ≠ Finset.univ := by
        intro hB
        apply hU
        apply (Finset.card_eq_iff_eq_univ A).mp
        calc A.card = B.card := hcard
          _ = Fintype.card Ω' := by simp [hB, Finset.card_univ]
          _ = Fintype.card Ω := hΩ.symm
      simp [score, hA, hU, hBne, hBu]

/-- R3 (irrelevant product): multiplying the world space by an independent
finite factor does not change the plausibility of an event. -/
theorem irrelevant_product {Ω Γ : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] (A : Finset Ω) :
    score A = score (A ×ˢ (Finset.univ : Finset Γ)) := by
  by_cases hA : A = ∅
  · have hprod : A ×ˢ (Finset.univ : Finset Γ) = ∅ := by
      rw [hA, Finset.product_eq_empty]
      exact Or.inl rfl
    simp [score, hA]
  · by_cases hU : A = Finset.univ
    · have hprod : (Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Γ) =
          (Finset.univ : Finset (Ω × Γ)) := by
        ext p
        simp
      rw [hU, hprod]
      have hAe : (Finset.univ : Finset Ω) ≠ ∅ := by
        intro h
        exact (Finset.ne_empty_of_mem (Finset.mem_univ (Classical.arbitrary Ω))) h
      have hpe : (Finset.univ : Finset (Ω × Γ)) ≠ ∅ := by
        intro h
        exact (Finset.ne_empty_of_mem (Finset.mem_univ (Classical.arbitrary (Ω × Γ)))) h
      simp [score, hAe, hpe]
    · have hne1 : A ×ˢ (Finset.univ : Finset Γ) ≠ ∅ := by
        intro h
        rw [Finset.product_eq_empty] at h
        rcases h with hA' | hΓ
        · exact hA hA'
        · exact (Finset.ne_empty_of_mem (Finset.mem_univ (Classical.arbitrary Γ))) hΓ
      have hne2 : A ×ˢ (Finset.univ : Finset Γ) ≠ (Finset.univ : Finset (Ω × Γ)) := by
        intro h
        have hc := congrArg Finset.card h
        have hAproper : A ⊂ (Finset.univ : Finset Ω) := by
          constructor
          · exact Finset.subset_univ A
          · intro hunivA
            apply hU
            exact le_antisymm (Finset.subset_univ A) hunivA
        have hAlt : A.card < Fintype.card Ω := by
          have := Finset.card_lt_card hAproper
          simpa using this
        have hΓpos : 0 < Fintype.card Γ := Fintype.card_pos
        have hmul : A.card * Fintype.card Γ < Fintype.card Ω * Fintype.card Γ := by
          exact (Nat.mul_lt_mul_right hΓpos).mpr hAlt
        rw [Finset.card_product] at hc
        have hc2 : A.card * Fintype.card Γ = Fintype.card Ω * Fintype.card Γ := by
          simpa [Finset.card_univ, Fintype.card_prod] using hc
        exact ne_of_lt hmul hc2
      simp [score, hA, hU, hne1, hne2]

/-- R4 (strict monotonicity) **fails** for this score: in `Fin 3`, the event
`{0}` is a strict subset of `{0, 1}`, yet both score `unknownV`, which is not
strictly less than itself.  This is precisely the obstruction to `threeSystem`
being a `PlausibilitySystem`. -/
theorem not_strictMono : ¬ ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {A B : Finset Ω}, A ⊂ B → score A < score B := by
  intro h
  let A : Finset (Fin 3) := {0}
  let B : Finset (Fin 3) := insert 1 ({0} : Finset (Fin 3))
  have hAB : A ⊂ B := by
    dsimp [A, B]
    constructor
    · intro x hx
      simp [hx]
    · intro hEq
      have h1m : (1 : Fin 3) ∈ insert 1 ({0} : Finset (Fin 3)) := by simp
      have h1' : (1 : Fin 3) ∈ ({0} : Finset (Fin 3)) := hEq h1m
      have h10 : (1 : Fin 3) = 0 := by simp at h1' ⊢
      have : (1 : Fin 3) ≠ 0 := by decide
      exact this h10
  have hscore := h hAB
  have hAscore : score A = ThreeVal.unknownV := by
    dsimp [A]
    have hne : ({0} : Finset (Fin 3)) ≠ ∅ := by
      intro he; simp at he
    have hu : ({0} : Finset (Fin 3)) ≠ (Finset.univ : Finset (Fin 3)) := by
      intro he
      have hc := congrArg Finset.card he
      rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hc
      norm_num at hc
    simp [score, hne, hu]
  have hBscore : score B = ThreeVal.unknownV := by
    dsimp [B]
    have hne : insert 1 ({0} : Finset (Fin 3)) ≠ ∅ := by
      intro he; simp at he
    have hu : insert 1 ({0} : Finset (Fin 3)) ≠ (Finset.univ : Finset (Fin 3)) := by
      intro he
      have hc := congrArg Finset.card he
      have hBcard : (insert 1 ({0} : Finset (Fin 3)) : Finset (Fin 3)).card = 2 := by
        have h10 : (1 : Fin 3) ≠ 0 := by decide
        simp [h10]
      rw [hBcard, Finset.card_univ, Fintype.card_fin] at hc
      norm_num at hc
    simp [score, hne, hu]
  rw [hAscore, hBscore] at hscore
  exact lt_irrefl _ hscore

end threeSystem

/-- A nonuniform example: the framework is not limited to uniform probability
distributions.  Ten microstates (`Fin 10`), of which the eight with
`i.val < 8` are favourable to "heads", give the counting-measure score
`8/10 = 4/5`. -/
theorem biased_coin_heads :
    (Plausibility.countSystem.{0}).score
      ((Finset.univ.filter (fun i : Fin 10 => i.val < 8)) : Finset (Fin 10)) =
      (4 : ℚ) / 5 := by
  have hcard : ((Finset.univ.filter (fun i : Fin 10 => i.val < 8)) : Finset (Fin 10)).card = 8 := by
    native_decide
  have hΩ : Fintype.card (Fin 10) = 10 := by simp
  dsimp [Plausibility.countSystem]
  rw [hcard, hΩ]
  norm_num

end Plausibility
