/-
The probability representation theorem (Van Horn's Theorem 14, semantic layer):
every plausibility system scores each event exactly as its rational
probability, and the achieved plausibility values are order-isomorphic to the
rational probabilities in `[0, 1]`.

We also include the counting-measure system, proving the requirements
consistent (Van Horn's Theorem 16), and the bridge from propositional problems
to finite-world events.
-/

import Plausibility.RationalRepresentation
import Plausibility.PropLogic.Semantics

namespace Plausibility

universe u v

set_option linter.unusedSectionVars false
set_option autoImplicit false

variable {P : Type v} [PartialOrder P] (sys : PlausibilitySystem P)

open PlausibilitySystem

section Prob

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The rational probability of an event: `#A / #Ω`, as an element of
`Rat01`. -/
noncomputable def probOf (A : Finset Ω) : Rat01 :=
  ⟨(A.card : ℚ) / Fintype.card Ω,
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.2 Fintype.card_pos)).2 (by
      exact_mod_cast card_le_card)⟩

@[simp]
theorem coe_probOf (A : Finset Ω) :
    ((probOf A : ℚ)) = (A.card : ℚ) / Fintype.card Ω := rfl

/-- **Theorem 14 (representation)**. The plausibility of an event is the
plausibility of its rational probability: `score A = upsilon₁ (#A / #Ω)`. -/
theorem score_eq_upsilon₁ (A : Finset Ω) :
    sys.score A = upsilon₁ sys (probOf A) := by
  calc sys.score A =
      upsilon₂ sys A.card (Fintype.card Ω) Fintype.card_pos card_le_card :=
        score_eq_canonical sys A
    _ = upsilon₁ sys (probOf A) :=
        (upsilon₁_eq_upsilon₂ sys A.card (Fintype.card Ω) Fintype.card_pos
          card_le_card).symm

end Prob

section IffCorollaries

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
  {Ω' : Type u} [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω']

/-- **Corollary 12**. Equal rational probabilities give equal plausibilities,
and conversely. -/
theorem score_eq_iff_probability_eq (A : Finset Ω) (B : Finset Ω') :
    sys.score A = sys.score B ↔
      (A.card : ℚ) / Fintype.card Ω = (B.card : ℚ) / Fintype.card Ω' := by
  rw [score_eq_upsilon₁ sys A, score_eq_upsilon₁ sys B]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : upsilon₁ sys (probOf A) < upsilon₁ sys (probOf B) :=
        upsilon₁_strictMono sys (by exact_mod_cast hlt)
      rw [h] at h1
      exact lt_irrefl _ h1
    · have h1 : upsilon₁ sys (probOf B) < upsilon₁ sys (probOf A) :=
        upsilon₁_strictMono sys (by exact_mod_cast hlt)
      rw [h] at h1
      exact lt_irrefl _ h1
  · intro h
    have hq : probOf A = probOf B := by
      apply Subtype.ext
      simp only [coe_probOf]
      exact h
    rw [hq]

/-- Strictly smaller rational probability gives strictly smaller plausibility,
and conversely. -/
theorem score_lt_iff_probability_lt (A : Finset Ω) (B : Finset Ω') :
    sys.score A < sys.score B ↔
      (A.card : ℚ) / Fintype.card Ω < (B.card : ℚ) / Fintype.card Ω' := by
  rw [score_eq_upsilon₁ sys A, score_eq_upsilon₁ sys B]
  constructor
  · intro h
    by_contra hcon
    rcases lt_or_eq_of_le (not_lt.mp hcon) with hlt | heq
    · have h1 : upsilon₁ sys (probOf B) < upsilon₁ sys (probOf A) :=
        upsilon₁_strictMono sys (by exact_mod_cast hlt)
      exact absurd h1 (lt_asymm h)
    · have hq2 : probOf B = probOf A := Subtype.ext heq
      rw [hq2] at h
      exact lt_irrefl _ h
  · intro hlt
    exact upsilon₁_strictMono sys (by exact_mod_cast hlt)

end IffCorollaries

namespace PlausibilitySystem

/-- The set of achievable plausibility values: the semantic version of Van
Horn's `P` (Definition 4).  It ranges over world spaces of *all* finite sizes,
so it can realize every rational probability. -/
def PlausibilityRange (sys : PlausibilitySystem.{u, v} P) : Set P :=
  {p | ∃ (Ω : Type u) (_ : Fintype Ω) (_ : DecidableEq Ω) (_ : Nonempty Ω)
      (A : Finset Ω), sys.score A = p}

theorem range_upsilon₁_eq :
    Set.range (upsilon₁ (P := P) sys) = sys.PlausibilityRange := by
  apply Set.eq_of_subset_of_subset
  · rintro p ⟨q, rfl⟩
    exact ⟨ULift (Fin ((q : ℚ).den)), inferInstance, inferInstance,
      ⟨ULift.up ⟨0, (q : ℚ).den_pos⟩⟩,
      canonicalEvent ((q : ℚ).num.natAbs) ((q : ℚ).den), rfl⟩
  · rintro p ⟨Ω, _, _, _, A, rfl⟩
    exact ⟨probOf A, (score_eq_upsilon₁ sys A).symm⟩

/-- **Theorem 14 (order isomorphism)**. The achieved plausibility values — not
an arbitrary ambient order — are order-isomorphic to the rational
probabilities in `[0, 1]`.  `P` is only a partial order; the linear order on
the achieved values is *derived*, not assumed. -/
noncomputable def plausibilityOrderIso :
    Rat01 ≃o (↥sys.PlausibilityRange) :=
  (upsilon₁_strictMono sys).orderIso (upsilon₁ (P := P) sys) |>.trans
    (OrderIso.setCongr _ _ (range_upsilon₁_eq sys))

/-- The isomorphism sends the rational probability of an event to its
plausibility value. -/
theorem plausibilityOrderIso_apply {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] (A : Finset Ω) :
    plausibilityOrderIso sys (probOf A) =
      ⟨sys.score A, ⟨Ω, inferInstance, inferInstance, ‹Nonempty Ω›, A, rfl⟩⟩ := by
  have h1 : ∀ q : Rat01, ((plausibilityOrderIso sys q : ↥sys.PlausibilityRange) : P) =
      upsilon₁ sys q := by
    intro q
    simp [plausibilityOrderIso]
  apply Subtype.ext
  rw [h1 (probOf A)]
  exact (score_eq_upsilon₁ sys A).symm
end PlausibilitySystem

section Consistency

/-- The counting-measure plausibility system: `score A := #A / #Ω` in `ℚ`.
This proves the requirements consistent (Van Horn's Theorem 16): they are
jointly satisfiable, so the representation theorem is not vacuous. -/
noncomputable def countSystem : PlausibilitySystem.{u, 0} ℚ where
  score := fun {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      (A : Finset Ω) => (A.card : ℚ) / Fintype.card Ω
  equiv_invariance :=
    fun {Ω Ω' : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω'] (A : Finset Ω) (B : Finset Ω')
      h => by
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
    rw [hcard, hΩ]
  irrelevant_product :=
    fun {Ω Γ : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] (A : Finset Ω) => by
    have hΓ : (0 : ℚ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
    rw [Finset.card_product, Finset.card_univ, Fintype.card_prod]
    field_simp
    push_cast
    ring
  strict_mono :=
    fun {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
      {A B : Finset Ω} hAB => by
    have h1 : A.card < B.card := Finset.card_lt_card hAB
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos
    have h2 : (0 : ℚ) < Fintype.card Ω := Nat.cast_pos.2 hΩpos
    rw [div_lt_div_iff₀ h2 h2]
    exact_mod_cast (Nat.mul_lt_mul_right hΩpos).mpr h1

end Consistency

section Bridge

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The event, within the world space of a satisfiable premise `X`, of worlds
that also satisfy the query `A`. -/
def eventOf (A X : Formula α) : Finset {v : α → Bool // v ∈ models X} :=
  (models (A.and X)).attach.map
    ⟨fun v => ⟨v.1, models_and_subset A X v.2⟩,
      fun a b h => by
        injection h with h'
        exact Subtype.ext h'⟩

theorem card_eventOf (A X : Formula α) :
    (eventOf A X).card = (models (A.and X)).card := by
  rw [eventOf, Finset.card_map, Finset.card_attach]

/-- **Bridge (milestone 9)**. The plausibility of a propositional query `A`
against a satisfiable premise `X` — scoring the event of `X`-worlds satisfying
`A` — equals the plausibility of the logical probability
`#models (A ∧ X) / #models X`. -/
theorem score_eventOf (sys : PlausibilitySystem P) (A X : Formula α)
    (hX : Satisfiable X)
    (instF : Fintype {v : α → Bool // v ∈ models X} := inferInstance)
    (instD : DecidableEq {v : α → Bool // v ∈ models X} := inferInstance)
    (instN : Nonempty {v : α → Bool // v ∈ models X} :=
      ⟨⟨hX.choose, hX.choose_spec⟩⟩) :
    sys.score (eventOf A X) =
      upsilon₁ sys ⟨logicalProbability A X hX, logicalProbability_nonneg A X hX,
        logicalProbability_le_one A X hX⟩ := by
  have hprob : probOf (eventOf A X) =
      ⟨logicalProbability A X hX, logicalProbability_nonneg A X hX,
        logicalProbability_le_one A X hX⟩ := by
    apply Subtype.ext
    rw [coe_probOf, card_eventOf, Fintype.card_coe]
    rfl
  rw [score_eq_upsilon₁ sys (eventOf A X), hprob]

end Bridge

section Sanity

variable (sys : PlausibilitySystem.{u, v} P)

/-- `(1,2)` and `(2,4)` have equal plausibility (Lemma 10). -/
example :
    PlausibilitySystem.upsilon₂ sys 2 4 (by norm_num) (by norm_num) =
      PlausibilitySystem.upsilon₂ sys 1 2 (by norm_num) (by norm_num) :=
  upsilon₂_scale sys 1 2 2 (by norm_num) (by norm_num) (by norm_num)

/-- `(1,3)` is strictly less plausible than `(1,2)` (Lemma 13). -/
example :
    PlausibilitySystem.upsilon₂ sys 1 3 (by norm_num) (by norm_num) <
      PlausibilitySystem.upsilon₂ sys 1 2 (by norm_num) (by norm_num) := by
  rw [← PlausibilitySystem.upsilon₁_eq_upsilon₂ sys 1 3 (by norm_num) (by norm_num),
    ← PlausibilitySystem.upsilon₁_eq_upsilon₂ sys 1 2 (by norm_num) (by norm_num)]
  exact upsilon₁_strictMono sys (by
    show ((⟨(1 : ℚ) / 3, by norm_num, by norm_num⟩ : Rat01) : ℚ) < 1 / 2
    norm_num)

end Sanity


end Plausibility
