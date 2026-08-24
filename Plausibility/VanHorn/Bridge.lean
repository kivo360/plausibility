/-
The final bridge: from a `LogicalPlausibility` satisfying the syntactic
Requirements R1–R4, construct a semantic `PlausibilitySystem`, so that
Theorem 14 (the probability representation and order isomorphism) applies
verbatim to the raw Requirements.

Contents:
* model-counting for `exactlyOne` and conjunctions over disjoint vocabularies;
* syntactic Lemma 10 (scale invariance from R3) on canonical problems;
* canonical strict monotonicity from R4;
* `toSystem : LogicalPlausibility P → PlausibilitySystem P` and the
  calibration theorem for propositional problems.
-/

import Plausibility.VanHorn.Reduction
import Plausibility.ProbabilityTheorem

namespace Plausibility

open Formula

universe v

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ### Counting models of `exactlyOne` -/

/-- The total valuation that makes exactly the atom `a` true. -/
def valAt (a : Atom) : Atom → Bool := fun x => decide (x = a)

/-- Any prefix-initial segment of a list is duplicate-free if the list is. -/
theorem nodup_take' {l : List Atom} (hl : l.Nodup) : ∀ j : ℕ, (l.take j).Nodup := by
  intro j
  induction j generalizing l with
  | zero => exact List.nodup_nil
  | succ j' ih =>
      cases l with
      | nil => exact List.nodup_nil
      | cons a l' =>
          rw [List.take_succ_cons]
          refine List.nodup_cons.mpr ⟨?_, ?_⟩
          · intro hmem
            exact (List.nodup_cons.mp hl).1 (List.mem_of_mem_take hmem)
          · exact ih ((List.nodup_cons.mp hl).2)

/-- Every model of `exactlyOne l` over `l.toFinset` has a unique true atom. -/
theorem existsUnique_true_of_mem_modelsOn {l : List Atom} {hl : l.Nodup}
    {w : {x // x ∈ l.toFinset} → Bool}
    (hw : w ∈ modelsOn l.toFinset (exactlyOne l)) :
    ∃ a, a ∈ l ∧ fillTrue l.toFinset w a = true ∧
      ∀ a' ∈ l, fillTrue l.toFinset w a' = true → a' = a := by
  have hsupp : (exactlyOne l).support ⊆ l.toFinset := support_exactlyOne_subset l
  have hev := (mem_modelsOn_iff l.toFinset (exactlyOne l) hsupp w).mp hw
  obtain ⟨a, ha, hva, huniq⟩ := (eval_exactlyOne_iff (fillTrue l.toFinset w) l hl).mp hev
  exact ⟨a, ha, hva, fun a' ha' hva' => huniq a' ha' hva'⟩

theorem mem_modelsOn_restrictFill_valAt {l : List Atom} {hl : l.Nodup} {a : Atom}
    (ha : a ∈ l) :
    restrictFill l.toFinset (valAt a) ∈ modelsOn l.toFinset (exactlyOne l) := by
  have hsupp : (exactlyOne l).support ⊆ l.toFinset := support_exactlyOne_subset l
  rw [mem_modelsOn_iff l.toFinset (exactlyOne l) hsupp,
    eval_restrictFill l.toFinset (exactlyOne l) hsupp (valAt a)]
  refine (eval_exactlyOne_iff (valAt a) l hl).mpr ⟨a, ha, by simp [valAt], ?_⟩
  intro a' _ hv
  simpa [valAt] using hv

theorem card_modelsOn_exactlyOne (l : List Atom) (hl : l.Nodup) :
    (modelsOn l.toFinset (exactlyOne l)).card = l.length := by
  classical
  -- the unique true atom of a model
  have hC : ∀ w : {w // w ∈ modelsOn l.toFinset (exactlyOne l)},
      ∃ a, a ∈ l ∧ fillTrue l.toFinset w.1 a = true ∧
        ∀ a' ∈ l, fillTrue l.toFinset w.1 a' = true → a' = a :=
    fun w => existsUnique_true_of_mem_modelsOn (l := l) (hl := hl) w.2
  -- key: any model agrees with valAt of its unique atom, on all of l.toFinset
  have hagree : ∀ (w : {w // w ∈ modelsOn l.toFinset (exactlyOne l)}) (x : Atom)
      (hx : x ∈ l),
      fillTrue l.toFinset w.1 x = decide (x = Classical.choose (hC w)) := by
    intro w x hx
    obtain ⟨hch, hvc, huniqc⟩ := Classical.choose_spec (hC w)
    cases hc : fillTrue l.toFinset w.1 x with
    | true => rw [decide_eq_true (huniqc x hx hc)]
    | false =>
        by_contra hcon
        have hxe : x = Classical.choose (hC w) := by simpa using hcon
        rw [hxe] at hc
        exact Bool.noConfusion (hc.symm.trans hvc)
  -- the two maps
  let hF : {w // w ∈ modelsOn l.toFinset (exactlyOne l)} → {a // a ∈ l.toFinset} :=
    fun w => ⟨Classical.choose (hC w),
      List.mem_toFinset.mpr (Classical.choose_spec (hC w)).1⟩
  let hG : {a // a ∈ l.toFinset} → {w // w ∈ modelsOn l.toFinset (exactlyOne l)} :=
    fun a => ⟨restrictFill l.toFinset (valAt a.1),
      mem_modelsOn_restrictFill_valAt (l := l) (hl := hl) (List.mem_toFinset.mp a.2)⟩
  have hFG : ∀ a, hF (hG a) = a := by
    intro a
    have hmem := mem_modelsOn_restrictFill_valAt (l := l) (hl := hl)
      (List.mem_toFinset.mp a.2)
    obtain ⟨b, hb, hvb, huniq⟩ := existsUnique_true_of_mem_modelsOn (l := l) (hl := hl) hmem
    have hfb : fillTrue l.toFinset (restrictFill l.toFinset (valAt a.1)) b
        = decide (b = a.1) := by
      simp only [fillTrue, restrictFill, valAt]
      rw [dif_pos (List.mem_toFinset.mpr hb)]
    have hba : b = a.1 := by
      rw [hfb] at hvb
      simpa using hvb
    have hcb : Classical.choose (existsUnique_true_of_mem_modelsOn (l := l)
        (hl := hl) hmem) = b := by
      have hs := Classical.choose_spec (existsUnique_true_of_mem_modelsOn (l := l)
        (hl := hl) hmem)
      exact ((hs.2.2 b hb (by rw [hfb, hba]; simp))).symm
    apply Subtype.ext
    show Classical.choose (existsUnique_true_of_mem_modelsOn (l := l) (hl := hl) hmem) = a.1
    rw [hcb, hba]
  have hGF : ∀ w, hG (hF w) = w := by
    intro w
    apply Subtype.ext
    funext x
    show restrictFill l.toFinset (valAt (Classical.choose (hC w))) x = _
    rw [restrictFill, valAt, ← hagree w x.1 (List.mem_toFinset.mp x.2)]
    simp only [fillTrue]
    rw [dif_pos x.2]
  have heq : {w // w ∈ modelsOn l.toFinset (exactlyOne l)} ≃ {a // a ∈ l.toFinset} :=
    ⟨hF, hG, hGF, hFG⟩
  rw [← Fintype.card_coe (modelsOn l.toFinset (exactlyOne l)),
    Fintype.card_congr heq, Fintype.card_coe, List.card_toFinset,
    List.dedup_eq_self.mpr hl]
/-! ### Splitting counts over disjoint vocabularies -/

section Split

variable (t v : List Atom)

/-- The total valuation determined by a `t`-part and a `v`-part. -/
def valJoin (p : {x // x ∈ t.toFinset} → Bool) (q : {x // x ∈ v.toFinset} → Bool) :
    Atom → Bool :=
  fun x => if h : x ∈ t.toFinset then fillTrue t.toFinset p x
    else if h' : x ∈ v.toFinset then fillTrue v.toFinset q x
    else true

variable {t v}

theorem eval_congr_of_forget (φ : Formula Atom) (hsupp : φ.support ⊆ t.toFinset)
    (u₁ u₂ : Atom → Bool) (h : ∀ x ∈ t.toFinset, u₁ x = u₂ x) :
    φ.eval u₁ = φ.eval u₂ :=
  eval_congr (fun x hx => h x (hsupp hx))

theorem card_modelsOn_split (φ ψ : Formula Atom)
    (ht : t.Nodup) (hv : v.Nodup) (hdisj : ∀ x ∈ t, x ∉ v)
    (hφ : φ.support ⊆ t.toFinset) (hψ : ψ.support ⊆ v.toFinset) :
    (modelsOn ((t ++ v).toFinset) (φ.and ψ)).card =
      (modelsOn t.toFinset φ).card * (modelsOn v.toFinset ψ).card := by
  classical
  set S' := (t ++ v).toFinset with hS'
  have hSt : ∀ x ∈ t, x ∈ S' := by
    intro x hx
    rw [hS', List.mem_toFinset]
    exact List.mem_append_left _ hx
  have hSv : ∀ x ∈ v, x ∈ S' := by
    intro x hx
    rw [hS', List.mem_toFinset]
    exact List.mem_append_right _ hx
  have hStF : t.toFinset ⊆ S' := fun x hx => hSt x (List.mem_toFinset.mp hx)
  have hSvF : v.toFinset ⊆ S' := fun x hx => hSv x (List.mem_toFinset.mp hx)
  have hsuppS : (φ.and ψ).support ⊆ S' := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hStF (hφ h)
    · exact hSvF (hψ h)
  -- key pointwise facts
  have hfillS : ∀ (w : {x // x ∈ S'} → Bool) (x : Atom) (hx : x ∈ S'),
      fillTrue S' w x = w ⟨x, hx⟩ := by
    intro w x hx
    simp only [fillTrue]
    rw [dif_pos hx]
  have hfillt : ∀ (u : Atom → Bool) (x : Atom) (hx : x ∈ t.toFinset),
      fillTrue t.toFinset (restrictFill t.toFinset u) x = u x := by
    intro u x hx
    simp only [fillTrue, restrictFill]
    rw [dif_pos hx]
  have hfillv : ∀ (u : Atom → Bool) (x : Atom) (hx : x ∈ v.toFinset),
      fillTrue v.toFinset (restrictFill v.toFinset u) x = u x := by
    intro u x hx
    simp only [fillTrue, restrictFill]
    rw [dif_pos hx]
  -- membership characterization of the pair projection
  have hFmem : ∀ w : {x // x ∈ S'} → Bool,
      ((restrictFill t.toFinset (fillTrue S' w)) ∈ modelsOn t.toFinset φ ∧
        (restrictFill v.toFinset (fillTrue S' w)) ∈ modelsOn v.toFinset ψ) ↔
      w ∈ modelsOn S' (φ.and ψ) := by
    intro w
    rw [mem_modelsOn_iff t.toFinset φ hφ,
      mem_modelsOn_iff v.toFinset ψ hψ,
      mem_modelsOn_iff S' (φ.and ψ) hsuppS,
      eval_restrictFill t.toFinset φ hφ (fillTrue S' w),
      eval_restrictFill v.toFinset ψ hψ (fillTrue S' w), Formula.eval,
      Bool.and_eq_true_iff]
  -- roundtrip fact on S'
  have hroundS : ∀ (u : Atom → Bool) (x : Atom) (hx : x ∈ S'),
      fillTrue S' (restrictFill S' u) x = u x := by
    intro u x hx
    simp only [fillTrue, restrictFill]
    rw [dif_pos hx]
  -- the backward map
  have hGmem : ∀ (p : {x // x ∈ t.toFinset} → Bool)
      (hp : p ∈ modelsOn t.toFinset φ)
      (q : {x // x ∈ v.toFinset} → Bool)
      (hq : q ∈ modelsOn v.toFinset ψ),
      restrictFill S' (valJoin t v p q) ∈ modelsOn S' (φ.and ψ) := by
    intro p hp q hq
    rw [mem_modelsOn_iff S' (φ.and ψ) hsuppS,
      eval_restrictFill S' (φ.and ψ) hsuppS (valJoin t v p q), Formula.eval,
      eval_congr_of_forget φ hφ (valJoin t v p q) (fillTrue t.toFinset p)
        (fun x hx => by rw [valJoin, dif_pos hx]),
      eval_congr_of_forget ψ hψ (valJoin t v p q) (fillTrue v.toFinset q)
        (fun x hx => by
          rw [valJoin, dif_neg (fun hxc =>
            hdisj x (List.mem_toFinset.mp hxc) (List.mem_toFinset.mp hx)),
            dif_pos hx]),
      (mem_modelsOn_iff t.toFinset φ hφ p).mp hp,
      (mem_modelsOn_iff v.toFinset ψ hψ q).mp hq]
    rfl
  -- the forward map
  let F : {w // w ∈ modelsOn S' (φ.and ψ)} →
      {p // p ∈ modelsOn t.toFinset φ} × {q // q ∈ modelsOn v.toFinset ψ} :=
    fun w => (⟨restrictFill t.toFinset (fillTrue S' w), ((hFmem w.1).mpr w.2).1⟩,
      ⟨restrictFill v.toFinset (fillTrue S' w), ((hFmem w.1).mpr w.2).2⟩)
  let G : {p // p ∈ modelsOn t.toFinset φ} × {q // q ∈ modelsOn v.toFinset ψ} →
      {w // w ∈ modelsOn S' (φ.and ψ)} :=
    fun pq => ⟨restrictFill S' (valJoin t v pq.1.1 pq.2.1),
      hGmem pq.1.1 pq.1.2 pq.2.1 pq.2.2⟩
  have hFG : ∀ pq, F (G pq) = pq := by
    intro pq
    apply Prod.ext
    · apply Subtype.ext
      funext x
      show restrictFill t.toFinset (fillTrue S' (restrictFill S' (valJoin t v _ _))) x = _
      rw [restrictFill, hroundS _ x (hStF x.2), valJoin, dif_pos x.2]
      simp only [fillTrue]
      rw [dif_pos x.2]
    · apply Subtype.ext
      funext x
      show restrictFill v.toFinset (fillTrue S' (restrictFill S' (valJoin t v _ _))) x = _
      rw [restrictFill, hroundS _ x (hSvF x.2), valJoin]
      have hxt : x.1 ∉ t.toFinset := fun hxc =>
        hdisj x.1 (List.mem_toFinset.mp hxc) (List.mem_toFinset.mp x.2)
      rw [dif_neg hxt, dif_pos x.2]
      simp only [fillTrue]
      rw [dif_pos x.2]
  have hS'mem : ∀ x ∈ S', x ∈ t ∨ x ∈ v := by
    intro x hx
    rw [hS', List.mem_toFinset] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hGF : ∀ w, G (F w) = w := by
    intro w
    apply Subtype.ext
    funext x
    show restrictFill S' (valJoin t v _ _) x = _
    rw [restrictFill, valJoin]
    by_cases hxt : x.1 ∈ t.toFinset
    · rw [dif_pos hxt, hfillt _ _ (Finset.mem_coe.mpr hxt),
        hfillS _ x.1 x.2]
    · have hxv : x.1 ∈ v.toFinset := by
        rcases hS'mem x.1 x.2 with h | h
        · exact absurd (List.mem_toFinset.mpr h) hxt
        · exact List.mem_toFinset.mpr h
      rw [dif_neg hxt, dif_pos hxv, hfillv _ _ (Finset.mem_coe.mpr hxv),
        hfillS _ x.1 x.2]
  have hequiv : {w // w ∈ modelsOn S' (φ.and ψ)} ≃
      {p // p ∈ modelsOn t.toFinset φ} × {q // q ∈ modelsOn v.toFinset ψ} :=
    ⟨F, G, hGF, hFG⟩
  rw [← Fintype.card_coe (modelsOn S' (φ.and ψ)), Fintype.card_congr hequiv,
    Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]

end Split

/-! ### Favorable counts -/

theorem card_modelsOn_bigOr_and_exactlyOne (l lt : List Atom) (hl : l.Nodup)
    (hlt : lt.Nodup) (hsub : ∀ x ∈ lt, x ∈ l) :
    (modelsOn l.toFinset ((bigOr lt).and (exactlyOne l))).card = lt.length := by
  classical
  have hsuppB : (bigOr lt).support ⊆ l.toFinset :=
    (support_bigOr_subset lt).trans (fun x hx => List.mem_toFinset.mpr (hsub x
      (List.mem_toFinset.mp hx)))
  have hsuppE : (exactlyOne l).support ⊆ l.toFinset := support_exactlyOne_subset l
  -- reduce to a filtered count over exactlyOne-models
  rw [modelsOn_and_eq hsuppB hsuppE]
  -- the filter lands exactly on the models whose unique atom is in lt
  set M := modelsOn l.toFinset (exactlyOne l) with hM
  -- bijection with lt.toFinset
  have hC : ∀ w : {x // x ∈ M},
      ∃ a, a ∈ l ∧ fillTrue l.toFinset w.1 a = true ∧
        ∀ a' ∈ l, fillTrue l.toFinset w.1 a' = true → a' = a :=
    fun w => existsUnique_true_of_mem_modelsOn (l := l) (hl := hl) w.2
  have hagree : ∀ (w : {x // x ∈ M}) (x : Atom) (hx : x ∈ l),
      fillTrue l.toFinset w.1 x = decide (x = Classical.choose (hC w)) :=
    fun w x hx => by
    obtain ⟨hch, hvc, huniqc⟩ := Classical.choose_spec (hC w)
    cases hc : fillTrue l.toFinset w.1 x with
    | true => rw [decide_eq_true (huniqc x hx hc)]
    | false =>
        by_contra hcon
        have hxe : x = Classical.choose (hC w) := by simpa using hcon
        rw [hxe] at hc
        exact Bool.noConfusion (hc.symm.trans hvc)
  have hkey : ∀ w : {x // x ∈ M},
      (bigOr lt).eval (fillTrue l.toFinset w.1) = true ↔
      Classical.choose (hC w) ∈ lt.toFinset := by
    intro w
    rw [eval_bigOr_iff]
    constructor
    · rintro ⟨a, ha, hva⟩
      have hal : a ∈ l := hsub a ha
      have hca : Classical.choose (hC w) = a :=
        ((Classical.choose_spec (hC w)).2.2 a hal hva).symm
      rw [hca]
      exact List.mem_toFinset.mpr ha
    · intro hanl
      refine ⟨Classical.choose (hC w), List.mem_toFinset.mp hanl, ?_⟩
      rw [hagree w _ (hsub _ (List.mem_toFinset.mp hanl))]
      simp
  -- a model is determined by its unique atom
  have hdet : ∀ (w : {x // x ∈ M}) (u : {x // x ∈ M}),
      Classical.choose (hC w) = Classical.choose (hC u) → w.1 = u.1 := by
    intro w u hw
    funext x
    have hwf : w.1 x = fillTrue l.toFinset w.1 x.1 := by
      simp only [fillTrue]; rw [dif_pos x.2]
    have huf : u.1 x = fillTrue l.toFinset u.1 x.1 := by
      simp only [fillTrue]; rw [dif_pos x.2]
    rw [hwf, huf, hagree w x.1 (List.mem_toFinset.mp x.2),
      hagree u x.1 (List.mem_toFinset.mp x.2), hw]
  -- the filtered models are the image of the lt-constructions
  have himg : M.filter (fun w => (bigOr lt).eval (fillTrue l.toFinset w) = true) =
      Finset.image (fun (a : {x // x ∈ lt.toFinset}) =>
        restrictFill l.toFinset (valAt a.1)) Finset.univ := by
    ext w
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hwm, hcond⟩
      have hchlt : Classical.choose (hC ⟨w, hwm⟩) ∈ lt.toFinset :=
        (hkey ⟨w, hwm⟩).mp hcond
      refine ⟨⟨Classical.choose (hC ⟨w, hwm⟩), hchlt⟩, Finset.mem_univ _, ?_⟩
      have hch : Classical.choose (hC ⟨w, hwm⟩) ∈ l :=
        (Classical.choose_spec (hC ⟨w, hwm⟩)).1
      funext y
      have hyl : y.1 ∈ l := List.mem_toFinset.mp y.2
      have hwy : w y = fillTrue l.toFinset w y.1 := by
        simp only [fillTrue]
        rw [dif_pos y.2]
      rw [restrictFill, valAt, hwy, hagree ⟨w, hwm⟩ y.1 hyl]
    · intro ⟨a, _, hae⟩
      refine ⟨?_, ?_⟩
      · rw [← hae]
        exact mem_modelsOn_restrictFill_valAt (l := l) (hl := hl)
          (hsub a.1 (List.mem_toFinset.mp a.2))
      · rw [← hae, eval_bigOr_iff]
        refine ⟨a.1, List.mem_toFinset.mp a.2, ?_⟩
        simp only [fillTrue, restrictFill, valAt]
        rw [dif_pos (List.mem_toFinset.mpr (hsub a.1 (List.mem_toFinset.mp a.2)))]
        simp
  rw [himg, Finset.card_image_of_injOn]
  · rw [Finset.card_univ, Fintype.card_coe, List.card_toFinset]
    rw [List.dedup_eq_self.mpr hlt]
  · intro a _ b _ hab
    apply Subtype.ext
    have h1 := congrFun hab
      ⟨a.1, List.mem_toFinset.mpr (hsub a.1 (List.mem_toFinset.mp a.2))⟩
    simp only [restrictFill, valAt] at h1
    simp at h1
    simpa using h1

/-! ### Syntactic Lemma 10: scale invariance from R3 -/

section Scale

variable {P : Type v} [PartialOrder P] (lp : LogicalPlausibility P)

theorem exactlyOne_sat {v : List Atom} (hv : v.Nodup) (hvk : v ≠ []) :
    (exactlyOne v).Sat := by
  obtain ⟨a, va, rfl⟩ := List.ne_nil_iff_exists_cons.mp hvk
  have h1 : (exactlyOne (a :: va)).eval (valAt a) = true :=
    (eval_exactlyOne_iff (valAt a) (a :: va) hv).mpr
      ⟨a, List.mem_cons_self, by simp [valAt], fun a' _ hva' => by
        simpa [valAt] using hva'⟩
  exact ⟨valAt a, h1⟩

theorem mem_freshAtoms_iff {b n a : ℕ} :
    a ∈ freshAtoms b n ↔ b ≤ a ∧ a < b + n := by
  rw [freshAtoms, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Nat.le_add_right b i, Nat.add_lt_add_left (List.mem_range.mp hi) b⟩
  · rintro ⟨hle, hlt⟩
    have hr : a - b < n := by
      rw [Nat.sub_lt_iff_lt_add hle]
      omega
    refine ⟨a - b, List.mem_range.mpr hr, Nat.add_sub_cancel' hle⟩

theorem value_scale (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hmn : m ≤ n)
    (b₁ b₂ b₃ : ℕ) (hb₁ : b₁ + n + k ≤ b₃) (hb₂ : b₂ + k * n ≤ b₃) :
    lp.value (bigOr ((freshAtoms b₁ n).take m))
        (exactlyOne (freshAtoms b₁ n)) =
      lp.value (bigOr ((freshAtoms b₂ (k * n)).take (k * m)))
        (exactlyOne (freshAtoms b₂ (k * n))) := by
  have hn : n > 0 := hn
  set t := freshAtoms b₁ n with ht
  set w := freshAtoms (b₁ + n) k with hw
  set u := freshAtoms b₂ (k * n) with hu
  have htn : t.Nodup := freshAtoms_nodup b₁ n
  have hwn : w.Nodup := freshAtoms_nodup (b₁ + n) k
  have hun : u.Nodup := freshAtoms_nodup b₂ (k * n)
  have hwne : w ≠ [] := by
    intro hc
    have hwlen : 0 < w.length := by
      simp only [hw, freshAtoms, List.length_map, List.length_range]
      omega
    rw [hw] at hc hwlen
    rw [hc] at hwlen
    exact absurd hwlen (by simp)
  have htlne : t ≠ [] := by
    intro hc
    have h1 : 0 < t.length := by
      simp only [ht, freshAtoms, List.length_map, List.length_range]
      omega
    rw [ht] at hc h1
    rw [hc] at h1
    exact absurd h1 (by simp)
  -- disjointness of vocabularies
  have hdisj : ∀ x ∈ t, x ∉ w := by
    intro x hx hwx
    have h1 : x < b₁ + n := (mem_freshAtoms_iff.mp hx).2
    have h2 : b₁ + n ≤ x := (mem_freshAtoms_iff.mp hwx).1
    exact absurd (h2.trans_lt h1) (Nat.lt_irrefl _)
  -- Step A: R3 augments the premise with an independent exactlyOne
  have hdisjF : Disjoint (exactlyOne w).support
      ((bigOr (t.take m)).support ∪ (exactlyOne t).support) := by
    rw [Finset.disjoint_left]
    intro x hxw hxu
    have hxw' : x ∈ w := List.mem_toFinset.mp
      (support_exactlyOne_subset w hxw)
    rcases Finset.mem_union.mp hxu with hx1 | hx2
    · have h1 := support_bigOr_subset (t.take m) hx1
      rw [List.mem_toFinset] at h1
      exact hdisj _ (List.mem_of_mem_take h1) hxw'
    · have h2 := support_exactlyOne_subset t hx2
      rw [List.mem_toFinset] at h2
      exact hdisj _ h2 hxw'
  have hA : lp.value (bigOr (t.take m)) (exactlyOne t) =
      lp.value (bigOr (t.take m)) ((exactlyOne w).and (exactlyOne t)) := by
    refine (lp.r3 (bigOr (t.take m)) (exactlyOne t) (exactlyOne w)
      (exactlyOne_sat hwn hwne) ?_).symm
    rw [Finset.disjoint_right]
    intro x hxu hxw
    have hxw' : x ∈ w := List.mem_toFinset.mp
      (support_exactlyOne_subset w hxw)
    rcases Finset.mem_union.mp hxu with hx1 | hx2
    · have h1 := support_bigOr_subset (t.take m) hx1
      rw [List.mem_toFinset] at h1
      exact hdisj _ (List.mem_of_mem_take h1) hxw'
    · have h2 := support_exactlyOne_subset t hx2
      rw [List.mem_toFinset] at h2
      exact hdisj _ h2 hxw'
  -- Step B: reduce the augmented problem by counts, over S' := t ∪ w
  set S' := (t ++ w).toFinset with hS'
  have hsuppB : (bigOr (t.take m)).support ⊆ S' := by
    intro x hx
    have h1 := support_bigOr_subset (t.take m) hx
    rw [List.mem_toFinset] at h1 ⊢
    exact List.mem_append_left _ (List.mem_of_mem_take h1)
  have hsuppEt : (exactlyOne t).support ⊆ S' := by
    intro x hx
    have h2 := support_exactlyOne_subset t hx
    rw [List.mem_toFinset] at h2 ⊢
    exact List.mem_append_left _ h2
  have hsuppEw : (exactlyOne w).support ⊆ S' := by
    intro x hx
    have h3 := support_exactlyOne_subset w hx
    rw [List.mem_toFinset] at h3 ⊢
    exact List.mem_append_right _ h3
  -- counts of the augmented premise and query
  have hcountX : (modelsOn S' ((exactlyOne t).and (exactlyOne w))).card = n * k := by
    rw [card_modelsOn_split (φ := exactlyOne t) (ψ := exactlyOne w) htn hwn hdisj
      (support_exactlyOne_subset t) (support_exactlyOne_subset w),
      card_modelsOn_exactlyOne t htn, card_modelsOn_exactlyOne w hwn,
      show t.length = n from by simp only [ht, freshAtoms, List.length_map, List.length_range],
      show w.length = k from by simp only [hw, freshAtoms, List.length_map, List.length_range]]
  -- reassoc: counts are insensitive to the association of ∧
  have hre : (modelsOn S' ((bigOr (t.take m)).and
      ((exactlyOne t).and (exactlyOne w)))).card =
      (modelsOn S' (((bigOr (t.take m)).and (exactlyOne t)).and
        (exactlyOne w))).card := by
    congr 1
    ext x
    simp [modelsOn, Finset.mem_filter, Formula.eval, Bool.and_assoc]
  have hsuppAnd : ((bigOr (t.take m)).and (exactlyOne t)).support ⊆ t.toFinset := by
    intro x hx
    rcases (Finset.mem_union.mp hx) with h1 | h2
    · have h1' := support_bigOr_subset (t.take m) h1
      rw [List.mem_toFinset] at h1'
      exact List.mem_toFinset.mpr (List.mem_of_mem_take h1')
    · exact support_exactlyOne_subset t h2
  have htakeNodup : (t.take m).Nodup := nodup_take' htn m
  have htakeSub : ∀ x ∈ t.take m, x ∈ t := fun x hx => List.mem_of_mem_take hx
  have htl : t.length = n := by
    simp only [ht, freshAtoms, List.length_map, List.length_range]
  have hwl : w.length = k := by
    simp only [hw, freshAtoms, List.length_map, List.length_range]
  have htakel : (t.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left (hmn.trans_eq htl.symm)]
  have hcountA : (modelsOn S' ((bigOr (t.take m)).and
      ((exactlyOne t).and (exactlyOne w)))).card = m * k := by
    rw [hre, card_modelsOn_split (φ := (bigOr (t.take m)).and (exactlyOne t))
      (ψ := exactlyOne w) htn hwn hdisj hsuppAnd (support_exactlyOne_subset w),
      card_modelsOn_bigOr_and_exactlyOne t (t.take m) htn htakeNodup htakeSub,
      card_modelsOn_exactlyOne w hwn, htakel, hwl]
  -- Step B: reduce the augmented problem over S' with fresh base b₃
  have hS'mem : ∀ a ∈ S', a ∈ t ∨ a ∈ w := by
    intro a ha
    rw [hS', List.mem_toFinset] at ha
    rcases List.mem_append.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hb3 : (S' ∪ ((bigOr (t.take m)).support ∪
      ((exactlyOne w).and (exactlyOne t)).support)).sup id < b₃ := by
    refine Finset.sup_lt_iff (Nat.pos_of_ne_zero (by omega)) |>.mpr ?_
    intro a ha
    show a < b₃
    rcases Finset.mem_union.mp ha with h1 | h2
    · rcases hS'mem a h1 with h | h
      · rw [ht] at h
        have h' := (mem_freshAtoms_iff.mp h).2
        exact h'.trans_le (by omega)
      · rw [hw] at h
        have h' := (mem_freshAtoms_iff.mp h).2
        exact h'.trans_le (by omega)
    · rcases Finset.mem_union.mp h2 with h3 | h4
      · have h5 := support_bigOr_subset (t.take m) h3
        rw [List.mem_toFinset] at h5
        have h5' := List.mem_of_mem_take h5
        rw [ht] at h5'
        exact ((mem_freshAtoms_iff.mp h5').2).trans_le (by omega)
      · have h6 : a ∈ (exactlyOne w).support ∪ (exactlyOne t).support := h4
        rcases Finset.mem_union.mp h6 with h7 | h8
        · have h9 := support_exactlyOne_subset w h7
          rw [List.mem_toFinset] at h9
          rw [hw] at h9
          exact ((mem_freshAtoms_iff.mp h9).2).trans_le (by omega)
        · have h10 := support_exactlyOne_subset t h8
          rw [List.mem_toFinset] at h10
          rw [ht] at h10
          exact ((mem_freshAtoms_iff.mp h10).2).trans_le (by omega)
  -- support containment for the augmented problem
  have hsuppAX : (bigOr (t.take m)).support ⊆ S' ∧
      ((exactlyOne w).and (exactlyOne t)).support ⊆ S' := by
    constructor
    · intro x hx
      have h5 := support_bigOr_subset (t.take m) hx
      rw [List.mem_toFinset] at h5 ⊢
      exact List.mem_append_left _ (List.mem_of_mem_take h5)
    · intro x hx
      rcases Finset.mem_union.mp hx with h7 | h8
      · have h9 := support_exactlyOne_subset w h7
        rw [List.mem_toFinset] at h9 ⊢
        exact List.mem_append_right _ h9
      · have h10 := support_exactlyOne_subset t h8
        rw [List.mem_toFinset] at h10 ⊢
        exact List.mem_append_left _ h10
  -- Step B: reduce the augmented problem
  have hB := lemma6_counts lp hsuppAX.1 hsuppAX.2 b₃ hb3
  -- the counts appearing there are the augmented ones
  have hXaug : (modelsOn S' ((exactlyOne w).and (exactlyOne t))) =
      modelsOn S' ((exactlyOne t).and (exactlyOne w)) := by
    ext x
    simp [modelsOn, Finset.mem_filter, Formula.eval, Bool.and_comm]
  have hAax : (modelsOn S' ((bigOr (t.take m)).and ((exactlyOne w).and (exactlyOne t)))) =
      modelsOn S' ((bigOr (t.take m)).and ((exactlyOne t).and (exactlyOne w))) := by
    ext x
    simp [modelsOn, Finset.mem_filter, Formula.eval, Bool.and_comm]
  -- counts under the flipped order
  have hcountX' : (modelsOn S' ((exactlyOne w).and (exactlyOne t))).card = k * n := by
    rw [hXaug, hcountX, Nat.mul_comm]
  have hcountA' : (modelsOn S' ((bigOr (t.take m)).and
      ((exactlyOne w).and (exactlyOne t)))).card = k * m := by
    rw [hAax, hcountA, Nat.mul_comm]
  -- so the augmented problem reduces to the canonical (k*m, k*n) problem at b₃
  have hBval := hB
  rw [hcountX', hcountA'] at hBval
  -- Step C: reduce the u-side at the same base b₃
  have husupp : (bigOr (u.take (k * m))).support ⊆ u.toFinset ∧
      (exactlyOne u).support ⊆ u.toFinset :=
    ⟨fun x hx => by
        have h' := support_bigOr_subset (u.take (k * m)) hx
        rw [List.mem_toFinset] at h'
        exact List.mem_toFinset.mpr (List.mem_of_mem_take h'),
      support_exactlyOne_subset u⟩
  have hub3 : (u.toFinset ∪ ((bigOr (u.take (k * m))).support ∪
      (exactlyOne u).support)).sup id < b₃ := by
    refine Finset.sup_lt_iff (Nat.pos_of_ne_zero (by omega)) |>.mpr ?_
    intro a ha
    show a < b₃
    rcases Finset.mem_union.mp ha with h1 | h2
    · have h1' : a ∈ u := List.mem_toFinset.mp h1
      rw [hu] at h1'
      exact ((mem_freshAtoms_iff.mp h1').2).trans_le (by omega)
    · rcases Finset.mem_union.mp h2 with h3 | h4
      · have h5 := support_bigOr_subset (u.take (k * m)) h3
        rw [List.mem_toFinset] at h5
        have h5' := List.mem_of_mem_take h5
        rw [hu] at h5'
        exact ((mem_freshAtoms_iff.mp h5').2).trans_le (by omega)
      · have h6 := support_exactlyOne_subset u h4
        rw [List.mem_toFinset] at h6
        rw [hu] at h6
        exact ((mem_freshAtoms_iff.mp h6).2).trans_le (by omega)
  have hC := lemma6_counts lp husupp.1 husupp.2 b₃ hub3
  -- the u-side counts: exactlyOne has k*n models, favorable k*m
  have hucardX : (modelsOn u.toFinset (exactlyOne u)).card = k * n := by
    rw [card_modelsOn_exactlyOne u hun]
    simp only [hu, freshAtoms, List.length_map, List.length_range]
  have huNodupTake : (u.take (k * m)).Nodup := nodup_take' hun (k * m)
  have hucardA : (modelsOn u.toFinset ((bigOr (u.take (k * m))).and (exactlyOne u))).card
      = k * m := by
    rw [card_modelsOn_bigOr_and_exactlyOne u (u.take (k * m)) hun
      huNodupTake (fun x hx => List.mem_of_mem_take hx)]
    have hulen : u.length = k * n := by
      simp only [hu, freshAtoms, List.length_map, List.length_range]
    rw [List.length_take, Nat.min_eq_left (hulen ▸ Nat.mul_le_mul_left k hmn)]
  rw [hucardX, hucardA] at hC
  -- assemble
  calc lp.value (bigOr ((freshAtoms b₁ n).take m)) (exactlyOne (freshAtoms b₁ n))
      = lp.value (bigOr (t.take m)) (exactlyOne t) := by
        simp only [ht]
    _ = lp.value (bigOr (t.take m)) ((exactlyOne w).and (exactlyOne t)) := hA
    _ = lp.value (bigOr ((freshAtoms b₃ (k * n)).take (k * m)))
        (exactlyOne (freshAtoms b₃ (k * n))) := hBval
    _ = lp.value (bigOr (u.take (k * m))) (exactlyOne u) := hC.symm
    _ = lp.value (bigOr ((freshAtoms b₂ (k * n)).take (k * m)))
        (exactlyOne (freshAtoms b₂ (k * n))) := by
        simp only [hu]

/-- `bigOr l` under the valuation `valAt a` holds iff `a ∈ l`. -/
theorem eval_bigOr_valAt_iff (l : List Atom) (a : Atom) :
    (bigOr l).eval (valAt a) = true ↔ a ∈ l := by
  rw [eval_bigOr_iff]
  constructor
  · rintro ⟨x, hx, hvx⟩
    have : decide (x = a) = true := by simpa [valAt] using hvx
    rw [decide_eq_true_iff] at this
    exact this ▸ hx
  · intro ha
    exact ⟨a, ha, by simp [valAt]⟩

theorem take_subset_take' {l : List Atom} {i j : ℕ} (h : i ≤ j) :
    l.take i ⊆ l.take j := by
  induction l generalizing i j with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons a l ih =>
      intro x hx
      match i, j with
      | 0, _ => exact absurd hx (by simp)
      | _ + 1, 0 => exact absurd h (by simp)
      | i' + 1, j' + 1 =>
          simp only [List.take] at hx ⊢
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih (by simp at h; omega) hx')

-- a witness atom in take m' \\ take m exists
theorem exists_mem_take_not_mem_take {l : List Atom} (hl : l.Nodup)
    {m m' : ℕ} (hmm' : m < m') (hm'l : m' ≤ l.length) :
    ∃ a₀, a₀ ∈ l.take m' ∧ a₀ ∉ l.take m := by
  have hlTake : (l.take m').Nodup := nodup_take' hl m'
  have hsub : (l.take m).toFinset ⊆ (l.take m').toFinset :=
    fun x hx => List.mem_toFinset.mpr (take_subset_take' (by omega)
      (List.mem_toFinset.mp hx))
  have hcard : ((l.take m').toFinset).card = m' := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hlTake, List.length_take,
      Nat.min_eq_left hm'l]
  have hcardm : ((l.take m).toFinset).card = m := by
    have hmTake : (l.take m).Nodup := nodup_take' hl m
    rw [List.card_toFinset, List.dedup_eq_self.mpr hmTake, List.length_take,
      Nat.min_eq_left (by omega)]
  have hcardlt : ((l.take m).toFinset).card < ((l.take m').toFinset).card := by
    rw [hcardm, hcard]
    omega
  have hne : ((l.take m').toFinset \ (l.take m).toFinset).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have hsd : ((l.take m').toFinset \ (l.take m).toFinset).card = 0 := by
      rw [hc]; rfl
    have hint : (l.take m).toFinset ∩ (l.take m').toFinset = (l.take m).toFinset := by
      ext x
      constructor
      · exact fun hx => (Finset.mem_inter.mp hx).1
      · exact fun hx => Finset.mem_inter.mpr ⟨hx, hsub hx⟩
    rw [Finset.card_sdiff, hint, hcardm, hcard] at hsd
    omega
  obtain ⟨a₀, ha₀⟩ := hne
  rw [Finset.mem_sdiff] at ha₀
  exact ⟨a₀, List.mem_toFinset.mp ha₀.1,
    fun hc => ha₀.2 (List.mem_toFinset.mpr hc)⟩

-- evaluation of exactlyOne at valAt a₀ (a₀ ∈ t)
theorem eval_exactlyOne_valAt {t : List Atom} (htn : t.Nodup) {a₀ : Atom}
    (ha₀ : a₀ ∈ t) : (exactlyOne t).eval (valAt a₀) = true :=
  (eval_exactlyOne_iff (valAt a₀) t htn).mpr ⟨a₀, ha₀, by simp [valAt],
    fun a' _ hv => by simpa [valAt] using hv⟩

/-- **Canonical strict monotonicity (Lemma 13, R4 side)**: with the same total
count, more favorable cases means strictly larger plausibility. -/
theorem value_mono_canonical (m m' n : ℕ) (hmm' : m < m') (hm'n : m' ≤ n)
    (b : ℕ) :
    lp.value (bigOr ((freshAtoms b n).take m)) (exactlyOne (freshAtoms b n)) <
      lp.value (bigOr ((freshAtoms b n).take m')) (exactlyOne (freshAtoms b n)) := by
  set t := freshAtoms b n with ht
  have htn : t.Nodup := freshAtoms_nodup b n
  have hlen : t.length = n := by
    simp only [ht, freshAtoms, List.length_map, List.length_range]
  obtain ⟨a₀, ha₀m', ha₀nm⟩ := exists_mem_take_not_mem_take htn hmm'
    (by rw [hlen]; omega)
  -- under exactlyOne, query j holds iff the unique true atom lies in take j
  have key : ∀ (v : Atom → Bool) (j : ℕ), (exactlyOne t).eval v = true →
      (bigOr (t.take j)).eval v = true → ∀ a ∈ t, v a = true → a ∈ t.take j := by
    intro v j hv hbig a ha hva
    have hx := (eval_exactlyOne_iff v t htn).mp hv
    obtain ⟨a₁, -, hva₁, huniq⟩ := hx
    have haa : a = a₁ := huniq a ha hva
    obtain ⟨x, hx1, hx2⟩ := (eval_bigOr_iff v (t.take j)).mp hbig
    have hxa : x = a₁ := huniq x (List.mem_of_mem_take hx1) hx2
    have hax : a = x := haa.trans hxa.symm
    rw [hax]
    exact hx1
  have key' : ∀ (v : Atom → Bool) (j : ℕ), (exactlyOne t).eval v = true →
      (∀ a ∈ t, v a = true → a ∈ t.take j) → (bigOr (t.take j)).eval v = true := by
    intro v j hv hall
    have hx := (eval_exactlyOne_iff v t htn).mp hv
    obtain ⟨a₁, ha₁, hva₁, -⟩ := hx
    exact (eval_bigOr_iff v (t.take j)).mpr ⟨a₁, hall a₁ ha₁ hva₁, hva₁⟩
  refine lp.r4 (bigOr (t.take m)) (bigOr (t.take m')) (exactlyOne t) ?_ ?_
  · intro v hv
    have hcongr : ((bigOr (t.take m)).imp (bigOr (t.take m'))).eval v
        = (!(bigOr (t.take m)).eval v || (bigOr (t.take m')).eval v) := by
      simp only [Formula.imp, Formula.neg, Formula.and, Formula.eval]
      cases (bigOr (t.take m)).eval v <;> cases (bigOr (t.take m')).eval v <;> rfl
    rw [hcongr]
    cases h1 : (bigOr (t.take m)).eval v with
    | false => rfl
    | true =>
        have h2 := key v m hv h1
        have h3 : ∀ a ∈ t, v a = true → a ∈ t.take m' :=
          fun a ha hva => take_subset_take' (by omega) (h2 a ha hva)
        rw [key' v m' hv h3]
        rfl
  · intro hent
    -- evaluate the converse at valAt a₀
    have hv₀ : (exactlyOne t).eval (valAt a₀) = true :=
      eval_exactlyOne_valAt htn (List.mem_of_mem_take ha₀m')
    have himp₀ := hent (valAt a₀) hv₀
    have hbigm'₀ : (bigOr (t.take m')).eval (valAt a₀) = true :=
      (eval_bigOr_valAt_iff (t.take m') a₀).mpr ha₀m'
    have himpeq : ((bigOr (t.take m')).imp (bigOr (t.take m))).eval (valAt a₀)
        = true := himp₀
    -- unfold imp evaluation concretely
    have hcongr : ((bigOr (t.take m')).imp (bigOr (t.take m))).eval (valAt a₀)
        = (!(bigOr (t.take m')).eval (valAt a₀) || (bigOr (t.take m)).eval (valAt a₀)) := by
      simp only [Formula.imp, Formula.neg, Formula.and, Formula.eval]
      cases (bigOr (t.take m')).eval (valAt a₀) <;>
        cases (bigOr (t.take m)).eval (valAt a₀) <;> rfl
    rw [hcongr, hbigm'₀] at himpeq
    simp only [Bool.not_true, Bool.false_or] at himpeq
    exact ha₀nm ((eval_bigOr_valAt_iff (t.take m) a₀).mp himpeq)

end Scale

/-! ### The instance: from Requirements to a plausibility system -/

section Instance

variable {P : Type v} [PartialOrder P] (lp : LogicalPlausibility P)

/-- The canonical plausibility value of an event with `m` favorable cases out
of `n` (any fresh base works; scale invariance makes the choice irrelevant
up to R3). -/
noncomputable def canonicalValue (m n : ℕ) : P :=
  lp.value (bigOr ((freshAtoms 1 n).take m)) (exactlyOne (freshAtoms 1 n))

/-- **The bridge instance**: a `LogicalPlausibility` satisfying R1–R4 induces a
semantic `PlausibilitySystem`. -/
noncomputable def toSystem : PlausibilitySystem.{0, v} P where
  score A := canonicalValue lp A.card (Fintype.card _)
  equiv_invariance := by
    intro Ω Ω' _ _ _ _ _ _ A B h
    obtain ⟨e, he⟩ := h
    have hcard : A.card = B.card := by
      have se : ↥A ≃ ↥B :=
        Equiv.ofBijective (fun x => ⟨e x, (he x.1).1 x.2⟩)
          ⟨fun x y hxy => Subtype.ext (e.injective (Subtype.ext_iff.1 hxy)), fun y => by
            refine ⟨⟨e.symm y, ?_⟩, ?_⟩
            · exact (he (e.symm y.1)).2 (by rw [Equiv.apply_symm_apply]; exact y.2)
            · apply Subtype.ext
              simp [Equiv.apply_symm_apply]⟩
      rw [← Fintype.card_coe, ← Fintype.card_coe, Fintype.card_congr se]
    have hΩ : Fintype.card Ω = Fintype.card Ω' := Fintype.card_congr e
    rw [hcard, hΩ]
  irrelevant_product := by
    intro Ω Γ _ _ _ _ _ _ A
    have h1 : (A ×ˢ (Finset.univ : Finset Γ)).card = A.card * Fintype.card Γ := by
      rw [Finset.card_product, Finset.card_univ]
    have h2 : Fintype.card (Ω × Γ) = Fintype.card Ω * Fintype.card Γ := by
      rw [Fintype.card_prod]
    have hΓ : 0 < Fintype.card Γ := Fintype.card_pos
    have hΩ : 0 < Fintype.card Ω := Fintype.card_pos
    have hA : A.card ≤ Fintype.card Ω := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ A)
    -- scale invariance: (m, n) ~ (m*k, n*k) — transit through a common base
    set k := Fintype.card Γ with hk
    set m := A.card with hm
    set n := Fintype.card Ω with hn
    -- via value_scale with an intermediate base above both
    set B := max (1 + n + k) (1 + k * n) with hbB
    set B' := B + k * n + 1 with hbB'
    have hBle1 : 1 + n + k ≤ B := le_max_left _ _
    have hBle2 : 1 + k * n ≤ B := le_max_right _ _
    have hB1 : 1 + n + k ≤ B' := by omega
    have hB2 : B + k * n ≤ B' := by omega
    have hB2' : 1 + k * n ≤ B' := by omega
    calc canonicalValue lp A.card (Fintype.card Ω)
        = lp.value (bigOr ((freshAtoms 1 n).take m)) (exactlyOne (freshAtoms 1 n)) := rfl
      _ = lp.value (bigOr ((freshAtoms B (k * n)).take (k * m)))
          (exactlyOne (freshAtoms B (k * n))) :=
          value_scale lp m n k hΩ hΓ hA 1 B B' hB1 hB2
      _ = lp.value (bigOr ((freshAtoms 1 (k * n)).take (k * m)))
          (exactlyOne (freshAtoms 1 (k * n))) := by
          have e1 := value_scale lp m n k hΩ hΓ hA 1 B B' hB1 hB2
          have e2 := value_scale lp m n k hΩ hΓ hA 1 1 B' hB1 hB2'
          rw [← e2, ← e1]
      _ = canonicalValue lp (A ×ˢ (Finset.univ : Finset Γ)).card
          (Fintype.card (Ω × Γ)) := by
          rw [h1, h2, Nat.mul_comm n k, Nat.mul_comm m k]
          rfl
  strict_mono := by
    intro Ω _ _ _ A B hAB
    have h1 : A.card < B.card := Finset.card_lt_card hAB
    have h2 : B.card ≤ Fintype.card Ω := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ B)
    exact value_mono_canonical lp A.card B.card (Fintype.card Ω) h1 h2 1

end Instance

/-! ### The final theorem -/

-- the final assembly statement
section Final

variable {P : Type v} [PartialOrder P]

/-- **Van Horn's Theorem 14, full syntactic form**: for a plausibility function
on propositional problems satisfying R1–R4, the plausibility of `(A | X)` is
exactly the plausibility of its rational probability `#(A ∧ X) / #X` (model
counts over any finite support), via the induced `PlausibilitySystem`. -/
theorem vanHorn_calibration (lp : LogicalPlausibility P) {S : Finset Atom}
    {A X : Formula Atom} (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (hX : X.Sat)
    (instF : Fintype {w // w ∈ modelsOn S X} := inferInstance)
    (instD : DecidableEq {w // w ∈ modelsOn S X} := inferInstance)
    (instN : Nonempty {w // w ∈ modelsOn S X} := by
      obtain ⟨v, hv⟩ := hX
      exact ⟨restrictFill S v, by
        rw [mem_modelsOn_iff S X hsX]
        exact eval_restrictFill S X hsX v⟩) :
    lp.value A X =
      PlausibilitySystem.upsilon₁ (toSystem lp)
        (Plausibility.probOf
          ((modelsOn S X).attach.filter (fun w =>
            (w.val : ↥S → Bool) ∈ modelsOn S (A.and X)))) := by
  -- abbreviations
  set W := modelsOn S X with hW
  set E := W.attach.filter (fun w => (w.val : ↥S → Bool) ∈ modelsOn S (A.and X)) with hE
  -- the event count is the favorable count
  have hEcard : E.card = (modelsOn S (A.and X)).card := by
    have hfil : W.filter (fun w => w ∈ modelsOn S (A.and X)) =
        modelsOn S (A.and X) := by
      ext w
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact h2
      · intro h
        refine ⟨?_, h⟩
        rw [mem_modelsOn_iff S X hsX]
        have := (mem_modelsOn_iff S (A.and X) (Finset.union_subset hsA hsX) w).mp h
        rw [Formula.eval, Bool.and_eq_true_iff] at this
        exact this.2
    calc E.card = (W.attach.filter (fun w =>
            (w.val : ↥S → Bool) ∈ modelsOn S (A.and X))).card := rfl
      _ = (W.filter (fun w => w ∈ modelsOn S (A.and X))).card := by
          rw [Finset.filter_attach, Finset.card_map, Finset.card_attach]
      _ = (modelsOn S (A.and X)).card := by rw [hfil]
  -- step 1: the induced system's score of the event is the canonical value
  have hscore : (toSystem lp).score E =
      canonicalValue lp (modelsOn S (A.and X)).card (modelsOn S X).card := by
    show canonicalValue lp E.card (Fintype.card {w // w ∈ modelsOn S X}) = _
    rw [hEcard, Fintype.card_coe (modelsOn S X)]
  -- step 2: the semantic layer identifies score with upsilon₁ of probOf
  have hsem := score_eq_upsilon₁ (toSystem lp) E
  -- step 3: reduce lp.value A X to the canonical value (Lemma 6 + k=1 transport)
  have hn0 : 0 < (modelsOn S X).card := by
    refine Finset.card_pos.mpr ⟨restrictFill S (Classical.choose (id hX)), ?_⟩
    have hv : X.eval (Classical.choose (id hX)) = true :=
      Classical.choose_spec (id hX)
    refine (mem_modelsOn_iff S X hsX _).mpr ?_
    rw [eval_restrictFill S X hsX (Classical.choose (id hX))]
    exact hv
  have hmn : (modelsOn S (A.and X)).card ≤ (modelsOn S X).card := by
    rw [hfil]
    exact Finset.card_filter_le _ _
  set b : ℕ := (S ∪ (A.support ∪ X.support)).sup id + (modelsOn S X).card + 1
    with hbdef
  have hsup : (S ∪ (A.support ∪ X.support)).sup id < b := by
    rw [hbdef]
    omega
  have hred := lemma6_counts lp hsA hsX b hsup
  -- value_scale with k = 1 transports base b to base 1
  have hscale := value_scale lp (modelsOn S (A.and X)).card (modelsOn S X).card 1
    hn0 (Nat.zero_lt_one) hmn b 1 (b + (modelsOn S X).card + 1)
    (by rw [hbdef]; omega) (by omega)
  simp only [Nat.one_mul] at hscale
  -- combine: hred's RHS is at base b; hscale says base-b = base-1
  calc lp.value A X = lp.value
        (bigOr ((freshAtoms 1 (modelsOn S X).card).take
          (modelsOn S (A.and X)).card))
        (exactlyOne (freshAtoms 1 (modelsOn S X).card)) := by
          rw [hred]
          exact hscale
    _ = canonicalValue lp (modelsOn S (A.and X)).card (modelsOn S X).card := rfl
    _ = (toSystem lp).score E := hscore.symm
    _ = PlausibilitySystem.upsilon₁ (toSystem lp)
        (Plausibility.probOf ((modelsOn S X).attach.filter (fun w =>
          (w.val : ↥S → Bool) ∈ modelsOn S (A.and X)))) := hsem

end Final

end Plausibility
