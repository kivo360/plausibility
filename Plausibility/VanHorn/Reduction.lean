/-
The canonical reduction (Van Horn's Lemma 6) from the syntactic Requirements:
from R1 and R2, `value A X` depends only on the model counts of `A ∧ X` and
`X`.  This file builds the machinery: fresh atoms, iterated definitions
(R2), and the four reduction steps.
-/

import Plausibility.VanHorn.Requirements
import Plausibility.VanHorn.Canonic

namespace Plausibility

open Formula

universe v u w

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {P : Type v} [PartialOrder P] (lp : LogicalPlausibility P)

/-! ### Fresh atoms -/

/-- `n` distinct atoms, all at least `b`. -/
def freshAtoms (b n : ℕ) : List Atom := (List.range n).map (b + ·)

theorem freshAtoms_nodup (b n : ℕ) : (freshAtoms b n).Nodup := by
  exact List.Nodup.map (by intro x y h; simpa using h) List.nodup_range

theorem le_of_mem_freshAtoms {b n : ℕ} {a : Atom} (h : a ∈ freshAtoms b n) : b ≤ a := by
  rw [freshAtoms, List.mem_map] at h
  obtain ⟨k, _, rfl⟩ := h
  omega

theorem freshAtoms_disjoint (S : Finset Atom) {b n : ℕ} (hb : S.sup id < b) :
    ∀ a ∈ freshAtoms b n, a ∉ S := by
  intro a ha hS
  have h2 : a ≤ S.sup id := by simpa using Finset.le_sup (f := id) hS
  have h3 : b ≤ a := le_of_mem_freshAtoms ha
  exact Nat.not_le_of_gt (h2.trans_lt hb) h3

/-- Membership in the folded union of definition supports. -/
theorem mem_foldr_supports {l : List Atom} {Es : Atom → Formula Atom} {a : Atom}
    (h : a ∈ (l.map Es).foldr (fun φ acc => φ.support ∪ acc) ∅) :
    ∃ s ∈ l, a ∈ (Es s).support := by
  induction l with
  | nil => cases h
  | cons s l ih =>
      rw [List.map_cons, List.foldr_cons, Finset.mem_union] at h
      rcases h with h1 | h2
      · exact ⟨s, List.mem_cons_self, h1⟩
      · obtain ⟨s', hs', hm⟩ := ih h2
        exact ⟨s', List.mem_cons_of_mem s hs', hm⟩

/-! ### Iterated definitions (R2) -/

theorem value_and_assoc (A X Y : Formula Atom) :
    lp.value A (X.and Y) = lp.value A ((Formula.top.and X).and Y) := by
  refine lp.r1 (A := A) (B := A) (X := X.and Y) (Y := (Formula.top.and X).and Y) ?_ ?_
  · intro v
    simp [Formula.eval, Formula.top]
  · intro v _
    rfl

theorem value_premise_eqv (A X Y : Formula Atom) (h : X.Eqv Y) :
    lp.value A X = lp.value A Y :=
  lp.r1 (A := A) (B := A) (X := X) (Y := Y) h (fun v _ => rfl)

theorem value_congr_left (A B X : Formula Atom) (h : X.EqvAt A B) :
    lp.value A X = lp.value B X :=
  lp.r1 (A := A) (B := B) (X := X) (Y := X) (Eqv.refl X) h

/-- **Iterated R2.** Conjoining definitions for a list of pairwise-fresh
symbols leaves the plausibility unchanged. -/
theorem r2_many (l : List Atom) (Es : Atom → Formula Atom) (A X : Formula Atom)
    (hnodup : l.Nodup)
    (hfresh : ∀ s ∈ l, s ∉ A.support ∪ X.support)
    (hdefs : ∀ s ∈ l, ∀ s' ∈ l, s' ∉ (Es s).support) :
    lp.value A ((defsList l Es).and X) = lp.value A X := by
  induction l generalizing X with
  | nil =>
      calc lp.value A ((defsList [] Es).and X)
          = lp.value A X := value_premise_eqv lp A _ X (by
            intro v
            simp [Formula.eval, Formula.top, defsList, List.map_nil, List.foldr_nil])
  | cons a l ih =>
      have hn : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hnodupl : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hfreshl : ∀ s ∈ l, s ∉ A.support ∪ X.support := fun s hs =>
        hfresh s (List.mem_cons_of_mem a hs)
      have hdefsl : ∀ s ∈ l, ∀ s' ∈ l, s' ∉ (Es s).support := fun s hs s' hs' =>
        hdefs s (List.mem_cons_of_mem a hs) s' (List.mem_cons_of_mem a hs')
      -- fold the head definition in front
      have hsplit : lp.value A ((defsList (a :: l) Es).and X)
          = lp.value A (((Formula.atom a).iff (Es a)).and ((defsList l Es).and X)) := by
        refine value_premise_eqv lp A _ _ ?_
        intro v
        simp [defsList, Formula.eval, List.map_cons, List.foldr_cons,
          Formula.iff, Formula.imp, Formula.top, Bool.and_assoc]
      rw [hsplit]
      -- R2 at a
      have ha_fresh : a ∉ A.support ∪ ((defsList l Es).and X).support ∪ (Es a).support := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h12 | h4
        · rcases Finset.mem_union.mp h12 with h1 | h3
          · exact hfresh a List.mem_cons_self (Finset.mem_union.mpr (Or.inl h1))
          · -- a cannot be in the support of the tail definitions or of X
            rcases Finset.mem_union.mp h3 with h3' | h3x
            · have h5 := support_defsList l Es h3'
              rcases Finset.mem_union.mp h5 with h6 | h7
              · exact hn (List.mem_toFinset.mp h6)
              · obtain ⟨s, hs, hm⟩ := mem_foldr_supports h7
                exact hdefs s (List.mem_cons_of_mem a hs) a List.mem_cons_self hm
            · exact hfresh a List.mem_cons_self (Finset.mem_union.mpr (Or.inr h3x))
        · exact hdefs a List.mem_cons_self a List.mem_cons_self h4
      rw [lp.r2 a A ((defsList l Es).and X) (Es a) ha_fresh]
      exact ih X hnodupl hfreshl hdefsl

/-! ### Diagrams over a finite support -/

/-- Support is preserved under lifting, in the forward direction. -/
theorem Formula.support_mapLift {α β : Type u} [DecidableEq α] [DecidableEq β]
    (f : α → β) (φ : Formula α) : (φ.mapLift f).support ⊆ Finset.image f φ.support := by
  induction φ with
  | atom a =>
      intro x hx
      have hx' : x = f a := by
        have h1 : (Formula.mapLift f (Formula.atom a)).support = {f a} := rfl
        rwa [h1, Finset.mem_singleton] at hx
      exact Finset.mem_image.mpr ⟨a, Finset.mem_singleton.mpr rfl, hx'.symm⟩
  | bot => exact Finset.empty_subset _
  | neg p ih => intro x hx; exact ih hx
  | and p q ihp ihq =>
      intro x hx
      rw [show (p.and q).support = p.support ∪ q.support from rfl, Finset.image_union]
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (ihp h)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨b, hb, hbe⟩))
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (ihq h)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨b, hb, hbe⟩))

/-- The diagram of an `S`-valuation, as a formula over the global language. -/
noncomputable def ZFormula (S : Finset Atom) (ρ : ↥S → Bool) : Formula Atom :=
  Formula.mapLift (α := ↥S) (β := Atom) Subtype.val (diagram ρ)

theorem eval_ZFormula_iff (S : Finset Atom) (ρ : ↥S → Bool) (v : Atom → Bool) :
    (ZFormula S ρ).eval v = true ↔ (fun x : ↥S => v x.val) = ρ := by
  rw [ZFormula,
    Formula.eval_mapLift (α := ↥S) (β := Atom) Subtype.val v (diagram ρ), eval_diagram]
  exact Iff.rfl

theorem support_ZFormula_subset (S : Finset Atom) (ρ : ↥S → Bool) :
    (ZFormula S ρ).support ⊆ S := by
  intro a ha
  have h1 := Formula.support_mapLift (α := ↥S) (β := Atom) Subtype.val (diagram ρ) ha
  obtain ⟨b, _, hbe⟩ := Finset.mem_image.mp h1
  exact hbe ▸ b.2

/-! ### Zip-paired definitions -/

/-- Definitions pairing the atoms of `l` with the formulas of `Zs`. -/
noncomputable def defsZip (l : List Atom) (Zs : List (Formula Atom)) : Formula Atom :=
  (l.zip Zs).map (fun p => (Formula.atom p.1).iff p.2) |>.foldr Formula.and Formula.top

theorem mem_foldr_Zs_supports {Zs : List (Formula Atom)} {a : Atom}
    (h : a ∈ Zs.foldr (fun φ acc => φ.support ∪ acc) ∅) :
    ∃ z ∈ Zs, a ∈ z.support := by
  induction Zs with
  | nil => cases h
  | cons z Zs ih =>
      rw [List.foldr_cons, Finset.mem_union] at h
      rcases h with h1 | h2
      · exact ⟨z, List.mem_cons_self, h1⟩
      · obtain ⟨z', hs', hm⟩ := ih h2
        exact ⟨z', List.mem_cons_of_mem z hs', hm⟩

theorem mem_defsZip_support (l : List Atom) (Zs : List (Formula Atom)) {a : Atom}
    (h : a ∈ (defsZip l Zs).support) :
    a ∈ l.toFinset ∨ ∃ z ∈ Zs, a ∈ z.support := by
  induction l generalizing Zs with
  | nil =>
      have hz : defsZip [] Zs = Formula.top := rfl
      rw [hz] at h
      exact absurd h (by simp [Formula.top, Formula.support])
  | cons x l ih =>
      cases Zs with
      | nil =>
          have hz : defsZip (x :: l) [] = Formula.top := rfl
          rw [hz] at h
          exact absurd h (by simp [Formula.top, Formula.support])
      | cons z Zs' =>
          have h1' : a ∈ ((Formula.atom x).iff z).support ∪ (defsZip l Zs').support := h
          rcases Finset.mem_union.mp h1' with h1 | h2
          · have h3 := support_iff _ _ h1
            rcases Finset.mem_union.mp h3 with h4 | h5
            · simp only [Formula.support, Finset.mem_singleton] at h4
              subst h4
              exact Or.inl (List.mem_toFinset.mpr (by simp))
            · exact Or.inr ⟨z, List.mem_cons_self, h5⟩
          · rcases ih Zs' h2 with h6 | h7
            · exact Or.inl (List.mem_toFinset.mpr (List.mem_cons_of_mem x
                (List.mem_toFinset.mp h6)))
            · obtain ⟨z', hz', hm⟩ := h7
              exact Or.inr ⟨z', List.mem_cons_of_mem z hz', hm⟩

/-- **Iterated R2, zip form**: conjoining the definitions pairing `l` with
`Zs` (for pairwise-fresh atoms of `l`) leaves plausibility unchanged. -/
theorem r2_many_zip (l : List Atom) (Zs : List (Formula Atom)) (A X : Formula Atom)
    (hnodup : l.Nodup)
    (hfresh : ∀ s ∈ l, s ∉ A.support ∪ X.support)
    (hdefs : ∀ s ∈ l, ∀ a ∈ l, ∀ z ∈ Zs, a ∉ z.support) :
    lp.value A ((defsZip l Zs).and X) = lp.value A X := by
  induction l generalizing X Zs with
  | nil =>
      refine value_premise_eqv lp A _ X ?_
      intro v
      simp [Formula.eval, Formula.top, defsZip]
  | cons x l ih =>
      cases Zs with
      | nil =>
          refine value_premise_eqv lp A _ X ?_
          intro v
          simp [Formula.eval, Formula.top, defsZip]
      | cons z Zs' =>
          have hn : x ∉ l := (List.nodup_cons.mp hnodup).1
          have hnodupl : l.Nodup := (List.nodup_cons.mp hnodup).2
          have hfreshl : ∀ s ∈ l, s ∉ A.support ∪ X.support :=
            fun s hs => hfresh s (List.mem_cons_of_mem x hs)
          have hdefsl' : ∀ s ∈ l, ∀ a ∈ l, ∀ z' ∈ Zs', a ∉ z'.support :=
            fun s hs a ha z' hz' =>
              hdefs s (List.mem_cons_of_mem x hs) a (List.mem_cons_of_mem x ha)
                z' (List.mem_cons_of_mem z hz')
          have hsplit : lp.value A ((defsZip (x :: l) (z :: Zs')).and X)
              = lp.value A (((Formula.atom x).iff z).and ((defsZip l Zs').and X)) := by
            refine value_premise_eqv lp A _ _ ?_
            intro v
            have hzc : (x :: l).zip (z :: Zs') = (x, z) :: l.zip Zs' := rfl
            simp [defsZip, Formula.eval, hzc, List.map_cons, List.foldr_cons,
              Formula.iff, Formula.imp, Formula.top, Bool.and_assoc]
          rw [hsplit]
          have hx_fresh : x ∉ A.support ∪ ((defsZip l Zs').and X).support ∪ z.support := by
            intro hmem
            rcases Finset.mem_union.mp hmem with h12 | h4
            · rcases Finset.mem_union.mp h12 with h1 | h3
              · exact hfresh x List.mem_cons_self (Finset.mem_union.mpr (Or.inl h1))
              · rcases Finset.mem_union.mp h3 with h3' | h3x
                · rcases mem_defsZip_support l Zs' h3' with h6 | h7
                  · exact hn (List.mem_toFinset.mp h6)
                  · obtain ⟨z', hz', hm⟩ := h7
                    exact hdefs x List.mem_cons_self x List.mem_cons_self
                      z' (List.mem_cons_of_mem z hz') hm
                · exact hfresh x List.mem_cons_self (Finset.mem_union.mpr (Or.inr h3x))
            · exact hdefs x List.mem_cons_self x List.mem_cons_self
                z List.mem_cons_self h4
          rw [lp.r2 x A ((defsZip l Zs').and X) z hx_fresh]
          exact ih Zs' X hnodupl hfreshl hdefsl'

/-! ### Evaluation lemmas for the canonical formulas -/

theorem eval_iff_eq (v : Atom → Bool) (p q : Formula Atom) :
    (p.iff q).eval v = true ↔ p.eval v = q.eval v := by
  unfold Formula.iff
  simp only [Formula.imp, Formula.neg, Formula.and, Formula.eval]
  cases p.eval v <;> cases q.eval v <;> simp

theorem eval_defsZip_pairs (v : Atom → Bool) (ps : List (Atom × Formula Atom)) :
    ((ps.map (fun p => (Formula.atom p.1).iff p.2)).foldr Formula.and Formula.top).eval v
      = true ↔ ∀ p ∈ ps, v p.1 = (p.2).eval v := by
  induction ps with
  | nil =>
      simp only [List.map_nil, List.foldr_nil, Formula.top, Formula.neg,
        Formula.bot, Formula.eval, Bool.not_false, eq_self_iff_true, true_iff]
      intro p hp
      exact absurd hp (by simp)
  | cons p ps ih =>
      rw [List.map_cons, List.foldr_cons, Formula.eval, Bool.and_eq_true_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ p' hp'
        rcases List.mem_cons.mp hp' with rfl | hp''
        · exact (eval_iff_eq v _ _).mp h1
        · exact h2 p' hp''
      · intro h
        exact ⟨(eval_iff_eq v _ _).mpr (h p List.mem_cons_self),
          fun p' hp' => h p' (List.mem_cons_of_mem _ hp')⟩

theorem eval_defsZip_iff (v : Atom → Bool) (l : List Atom) (Zs : List (Formula Atom)) :
    (defsZip l Zs).eval v = true ↔
      ∀ p ∈ l.zip Zs, v p.1 = (p.2).eval v := by
  exact eval_defsZip_pairs v (l.zip Zs)

theorem support_bigOr_subset (l : List Atom) :
    (bigOr l).support ⊆ l.toFinset := by
  intro a ha
  induction l with
  | nil =>
      have h1 : (bigOr []).support = (∅ : Finset Atom) := rfl
      rw [h1] at ha
      exact absurd ha (by simp)
  | cons x l ih =>
      have h1 : (bigOr (x :: l)).support =
          ((Formula.atom x).or (bigOr l)).support := rfl
      rw [h1] at ha
      have h2 := support_or _ _ ha
      rw [Finset.mem_union] at h2
      rcases h2 with h3 | h4
      · simp only [Formula.support, Finset.mem_singleton] at h3
        exact List.mem_toFinset.mpr (by simp [h3])
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem x (List.mem_toFinset.mp (ih h4)))

theorem support_allNeg_subset (l : List Atom) :
    (allNeg l).support ⊆ l.toFinset := by
  intro a ha
  induction l with
  | nil =>
      have h1 : allNeg [] = Formula.top := rfl
      rw [h1] at ha
      exact absurd ha (by simp [Formula.top, Formula.neg, Formula.support])
  | cons x l ih =>
      have h1 : a ∈ (Formula.atom x).neg.support ∪ (allNeg l).support := ha
      rw [Finset.mem_union] at h1
      rcases h1 with h2 | h3
      · simp only [Formula.support, Finset.mem_singleton] at h2
        exact List.mem_toFinset.mpr (by simp [h2])
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem x
          (List.mem_toFinset.mp (ih h3)))

theorem support_exactlyOne_subset (l : List Atom) :
    (exactlyOne l).support ⊆ l.toFinset := by
  intro a ha
  induction l with
  | nil =>
      have h1 : exactlyOne [] = Formula.bot := rfl
      rw [h1] at ha
      exact absurd ha (by simp [Formula.support])
  | cons x l ih =>
      have h1 : a ∈ ((Formula.atom x).and (allNeg l)).support ∪
          ((Formula.atom x).neg.and (exactlyOne l)).support := ha
      rw [Finset.mem_union] at h1
      rcases h1 with h2 | h3
      · have h2' : a ∈ (Formula.atom x).support ∪ (allNeg l).support := h2
        rw [Finset.mem_union] at h2'
        rcases h2' with h4 | h5
        · simp only [Formula.support, Finset.mem_singleton] at h4
          exact List.mem_toFinset.mpr (by simp [h4])
        · exact List.mem_toFinset.mpr (List.mem_cons_of_mem x
            (List.mem_toFinset.mp (support_allNeg_subset l h5)))
      · have h3' : a ∈ (Formula.atom x).neg.support ∪ (exactlyOne l).support := h3
        rw [Finset.mem_union] at h3'
        rcases h3' with h4 | h5
        · have h4' : a ∈ (Formula.atom x).support := h4
          simp only [Formula.support, Finset.mem_singleton] at h4'
          exact List.mem_toFinset.mpr (by simp [h4'])
        · exact List.mem_toFinset.mpr (List.mem_cons_of_mem x
            (List.mem_toFinset.mp (ih h5)))

/-- A pair `(f p, g p)` lies in the zipped self-maps. -/
theorem mem_zip_map_self {α β γ : Type u} (f : α → β) (g : α → γ) :
    ∀ (ps : List α) {p : α}, p ∈ ps → (f p, g p) ∈ (ps.map f).zip (ps.map g)
  | [], _, hp => absurd hp (by simp)
  | q :: qs, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_zip_map_self f g qs hp')

theorem zip_map_self_eq {α β γ : Type u} (f : α → β) (g : α → γ) :
    ∀ ps : List α, ps.map (fun q => (f q, g q)) = (ps.map f).zip (ps.map g)
  | [] => rfl
  | q :: qs => by
      rw [List.map_cons, zip_map_self_eq f g qs]
      rfl

/-- Evaluation of the `t`-definitions, indexed by the pair list. -/
theorem eval_defsZip_ps_iff (S : Finset Atom) (v : Atom → Bool)
    (ps : List (Atom × (↥S → Bool))) :
    (defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).eval v = true ↔
      ∀ p ∈ ps, v p.1 = (ZFormula S p.2).eval v := by
  induction ps with
  | nil =>
      constructor
      · intro h p hp
        exact absurd hp (by simp)
      · intro _
        rfl
  | cons q qs ih =>
      have hc : defsZip ((q :: qs).map Prod.fst) ((q :: qs).map (fun p => ZFormula S p.2))
          = ((Formula.atom q.1).iff (ZFormula S q.2)).and
            (defsZip (qs.map Prod.fst) (qs.map (fun p => ZFormula S p.2))) := rfl
      rw [hc, Formula.eval, Bool.and_eq_true_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact (eval_iff_eq v _ _).mp h1
        · exact h2 p hp'
      · intro h
        exact ⟨(eval_iff_eq v _ _).mpr (h q List.mem_cons_self),
          fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

/-! ### Step 2: the query becomes a disjunction over the favorable symbols -/

section Step2

variable {S : Finset Atom} {A X : Formula Atom}

/-- Under the `t`-definitions, a valuation satisfies `A` exactly when it makes
one of the favorable symbols true. -/
theorem step2_eqvAt
    (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (ps : List (Atom × (↥S → Bool)))
    (hcover : ∀ w : ↥S → Bool, X.eval (fillTrue S w) = true ↔ w ∈ ps.map Prod.snd)
    (v : Atom → Bool)
    (hD : ((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v
      = true) :
    A.eval v = (bigOr (ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map
      Prod.fst)).eval v := by
  obtain ⟨hDdefs, hDX⟩ := Bool.and_eq_true_iff.mp hD
  set w : ↥S → Bool := restrictFill S v with hw
  -- the definitions force: v (p.1) = true ↔ p.2 = w
  have hZ : ∀ p ∈ ps, v p.1 = true ↔ p.2 = w := by
    intro p hp
    have hpair : (p.1, ZFormula S p.2) ∈
        (ps.map Prod.fst).zip (ps.map (fun q => ZFormula S q.2)) :=
      mem_zip_map_self Prod.fst (fun q => ZFormula S q.2) ps hp
    have h1 := (eval_defsZip_iff v _ _).mp hDdefs (p.1, ZFormula S p.2) hpair
    rw [h1, eval_ZFormula_iff]
    exact ⟨Eq.symm, Eq.symm⟩
  -- X holds of the restricted valuation, which therefore occurs in ps
  have hXw : X.eval (fillTrue S (restrictFill S v)) = true := by
    rw [eval_restrictFill S X hsX v]
    exact hDX
  have hwmem : restrictFill S v ∈ ps.map Prod.snd := (hcover _).mp hXw
  obtain ⟨p₀, hp₀, hp₀w⟩ := List.mem_map.mp hwmem
  have hp₀t : v p₀.1 = true := (hZ p₀ hp₀).mpr hp₀w
  -- the big disjunction agrees with A on the restricted valuation
  have hb : ((bigOr
        (ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map Prod.fst)).eval v
        = true) ↔ (A.eval (fillTrue S p₀.2) = true) := by
    rw [eval_bigOr_iff]
    constructor
    · rintro ⟨s, hs, hvs⟩
      obtain ⟨p, hpfilter, rfl⟩ := List.mem_map.mp hs
      have hp : p ∈ ps := (List.mem_filter.mp hpfilter).1
      have hpw : p.2 = restrictFill S v := (hZ p hp).mp hvs
      have hcond : A.eval (fillTrue S p.2) = true :=
        of_decide_eq_true (List.mem_filter.mp hpfilter).2
      rw [hpw, ← hp₀w] at hcond
      exact hcond
    · intro hAtrue
      refine ⟨p₀.1, List.mem_map.mpr ⟨p₀, ?_, rfl⟩, hp₀t⟩
      exact List.mem_filter.mpr ⟨hp₀, decide_eq_true hAtrue⟩
  -- conclude by Boolean case analysis
  cases hAv : A.eval v with
  | true =>
      have hAw : A.eval (fillTrue S p₀.2) = true := by
        rw [hp₀w, eval_restrictFill S A hsA v]
        exact hAv
      have hbig : (bigOr
        (ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map Prod.fst)).eval v
          = true := hb.mpr hAw
      rw [hbig]
  | false =>
      have hAw : ¬ A.eval (fillTrue S p₀.2) = true := by
        intro hc
        rw [hp₀w, eval_restrictFill S A hsA v] at hc
        rw [hAv] at hc
        exact Bool.noConfusion hc
      cases hO' : (bigOr
        (ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map Prod.fst)).eval v with
      | false => rfl
      | true => exact absurd (hb.mp hO') hAw

end Step2

/-! ### Step 3: define the original atoms back; premise becomes exactly-one -/

section Step3

variable {S : Finset Atom} {A X : Formula Atom}

/-- The definition of atom `a` as the disjunction of the `t`-symbols of the
valuations that make `a` true (defaulting to `top` outside `S`). -/
noncomputable def sBlock (ps : List (Atom × (↥S → Bool))) (a : Atom) : Formula Atom :=
  if h : a ∈ S then bigOr ((ps.filter (fun p => p.2 ⟨a, h⟩ = true)).map Prod.fst)
  else Formula.top

/-- The definitions of the atoms of `S` in terms of the `t`-symbols. -/
noncomputable def sDefs (ps : List (Atom × (↥S → Bool))) : Formula Atom :=
  defsZip S.toList (S.toList.map (fun a => sBlock ps a))

theorem eval_defsZip_map_iff (v : Atom → Bool) (l : List Atom) (f : Atom → Formula Atom) :
    (defsZip l (l.map f)).eval v = true ↔ ∀ a ∈ l, v a = (f a).eval v := by
  induction l with
  | nil =>
      refine ⟨fun _ a ha => absurd ha (by simp), ?_⟩
      intro _
      rfl
  | cons x l ih =>
      have hc : defsZip (x :: l) ((x :: l).map f) =
          ((Formula.atom x).iff (f x)).and (defsZip l (l.map f)) := rfl
      rw [hc, Formula.eval, Bool.and_eq_true_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact (eval_iff_eq v _ _).mp h1
        · exact h2 a ha'
      · intro h
        exact ⟨(eval_iff_eq v _ _).mpr (h x List.mem_cons_self),
          fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem eval_sDefs_iff (v : Atom → Bool) (ps : List (Atom × (↥S → Bool))) :
    (sDefs ps).eval v = true ↔ ∀ a ∈ S, v a = (sBlock ps a).eval v := by
  rw [sDefs, eval_defsZip_map_iff]
  constructor
  · intro h a ha
    exact h a (Finset.mem_toList.2 ha)
  · intro h a ha
    exact h a (Finset.mem_toList.mp ha)

/-- Under the `t`-definitions, the block of atom `a` evaluates to `v a`. -/
theorem eval_sBlock_eq
    (hsX : X.support ⊆ S)
    (v : Atom → Bool)
    (ps : List (Atom × (↥S → Bool)))
    (hZiff : ∀ p ∈ ps, (v p.1 = true ↔ p.2 = restrictFill S v))
    (hpairSnd : ∀ p ∈ ps, ∀ q ∈ ps, p.2 = q.2 → p = q)
    (hXv : X.eval v = true)
    (hcover : ∀ w : ↥S → Bool, X.eval (fillTrue S w) = true ↔ w ∈ ps.map Prod.snd)
    (a : Atom) (ha : a ∈ S) :
    (sBlock ps a).eval v = v a := by
  have hwmem : restrictFill S v ∈ ps.map Prod.snd := by
    refine (hcover _).mp ?_
    rw [eval_restrictFill S X hsX v]
    exact hXv
  obtain ⟨p₀, hp₀, hp₀w⟩ := List.mem_map.mp hwmem
  -- characterize the block evaluation
  have hblock : (sBlock ps a).eval v = true ↔ v a = true := by
    unfold sBlock
    rw [dif_pos ha, eval_bigOr_iff]
    constructor
    · rintro ⟨s, hs, hvs⟩
      obtain ⟨p, hpfilter, rfl⟩ := List.mem_map.mp hs
      have hp : p ∈ ps := (List.mem_filter.mp hpfilter).1
      have hpv : p.2 = restrictFill S v := (hZiff p hp).mp hvs
      have hdec : p.2 ⟨a, ha⟩ = true := of_decide_eq_true
        (List.mem_filter.mp hpfilter).2
      rw [show p = p₀ from hpairSnd p hp p₀ hp₀ (hpv.trans hp₀w.symm), hp₀w] at hdec
      exact hdec
    · intro hva
      have hva' : restrictFill S v ⟨a, ha⟩ = true := by
        show v a = true
        exact hva
      refine ⟨p₀.1, List.mem_map.mpr ⟨p₀, ?_, rfl⟩, (hZiff p₀ hp₀).mpr hp₀w⟩
      refine List.mem_filter.mpr ⟨hp₀, decide_eq_true ?_⟩
      rw [hp₀w]
      exact hva'
  cases hba : v a with
  | false =>
      cases hsb : (sBlock ps a).eval v with
      | false => rfl
      | true => exact absurd (hblock.mp hsb) (by rw [hba]; simp)
  | true =>
      cases hsb : (sBlock ps a).eval v with
      | true => rfl
      | false => exact absurd (hblock.mpr hba) (by rw [hsb]; simp)

theorem step3_premise_eqv
    (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (ps : List (Atom × (↥S → Bool)))
    (hcover : ∀ w : ↥S → Bool, X.eval (fillTrue S w) = true ↔ w ∈ ps.map Prod.snd)
    (hpairSnd : ∀ p ∈ ps, ∀ q ∈ ps, p.2 = q.2 → p = q)
    (hpairFst : ∀ p ∈ ps, ∀ q ∈ ps, p.1 = q.1 → p = q)
    (htnodup : (ps.map Prod.fst).Nodup)
    (v : Atom → Bool) :
    (((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v) =
      (((sDefs ps).and (exactlyOne (ps.map Prod.fst))).eval v) := by
  have hZall : ∀ (hD : (defsZip (ps.map Prod.fst)
        (ps.map (fun p => ZFormula S p.2))).eval v = true)
      (p : Atom × (↥S → Bool)) (hp : p ∈ ps),
      v p.1 = (ZFormula S p.2).eval v := by
    intro hD p hp
    exact (eval_defsZip_iff v _ _).mp hD (p.1, ZFormula S p.2)
      (mem_zip_map_self Prod.fst (fun q => ZFormula S q.2) ps hp)
  have hZiff : ∀ (hD : (defsZip (ps.map Prod.fst)
        (ps.map (fun p => ZFormula S p.2))).eval v = true)
      (p : Atom × (↥S → Bool)) (hp : p ∈ ps),
      (v p.1 = true ↔ p.2 = restrictFill S v) := by
    intro hD p hp
    have h1 := hZall hD p hp
    rw [h1, eval_ZFormula_iff]
    exact ⟨Eq.symm, Eq.symm⟩
  have e1 : (((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v
      = true) ↔ ((defsZip (ps.map Prod.fst)
        (ps.map (fun p => ZFormula S p.2))).eval v = true ∧ X.eval v = true) := by
    rw [show (((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v)
        = ((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).eval v && X.eval v)
        from rfl, Bool.and_eq_true_iff]
  have e2 : (((sDefs ps).and (exactlyOne (ps.map Prod.fst))).eval v = true) ↔
      ((sDefs ps).eval v = true ∧ (exactlyOne (ps.map Prod.fst)).eval v = true) := by
    rw [show (((sDefs ps).and (exactlyOne (ps.map Prod.fst))).eval v)
        = ((sDefs ps).eval v && (exactlyOne (ps.map Prod.fst)).eval v) from rfl,
      Bool.and_eq_true_iff]
  have key : ((((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v)
      = true) ↔ ((((sDefs ps).and (exactlyOne (ps.map Prod.fst))).eval v) = true) := by
    rw [e1, e2]
    constructor
    · rintro ⟨hDdefs, hDX⟩
      refine ⟨?_, ?_⟩
      · rw [eval_sDefs_iff]
        intro a ha
        exact (eval_sBlock_eq hsX v ps (hZiff hDdefs) hpairSnd hDX hcover a ha).symm
      · have hwmem : restrictFill S v ∈ ps.map Prod.snd := by
          refine (hcover _).mp ?_
          rw [eval_restrictFill S X hsX v]
          exact hDX
        obtain ⟨p₀, hp₀, hp₀w⟩ := List.mem_map.mp hwmem
        refine (eval_exactlyOne_iff v _ htnodup).mpr ⟨p₀.1,
          List.mem_map.mpr ⟨p₀, hp₀, rfl⟩, (hZiff hDdefs p₀ hp₀).mpr hp₀w, ?_⟩
        intro a' ha' hva'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
        have hq0 : q = p₀ := hpairSnd q hq p₀ hp₀
          (((hZiff hDdefs q hq).mp hva').trans hp₀w.symm)
        exact congrArg Prod.fst hq0
    · rintro ⟨hDs, hOne⟩
      -- the unique true t-symbol comes from some pair p₀
      obtain ⟨a₀, ha₀t, ha₀v, ha₀uniq⟩ := (eval_exactlyOne_iff v _ htnodup).mp hOne
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp ha₀t
      -- the restriction of v is p₀.2
      have hw : ∀ x : ↥S, restrictFill S v x = p₀.2 x := by
        intro x
        have hx := (eval_sDefs_iff v ps).mp hDs x.1 x.2
        have hblock : (sBlock ps x.1).eval v = true ↔ p₀.2 x = true := by
          unfold sBlock
          rw [dif_pos x.2, eval_bigOr_iff]
          constructor
          · rintro ⟨s, hs, hvs⟩
            obtain ⟨q, hqf, rfl⟩ := List.mem_map.mp hs
            have hq : q ∈ ps := (List.mem_filter.mp hqf).1
            have hs0 : q.1 = p₀.1 := ha₀uniq q.1
              (List.mem_map.mpr ⟨q, hq, rfl⟩) hvs
            have : q = p₀ := hpairFst q hq p₀ hp₀ hs0
            subst this
            exact of_decide_eq_true (List.mem_filter.mp hqf).2
          · intro hptrue
            refine ⟨p₀.1, List.mem_map.mpr ⟨p₀, ?_, rfl⟩, ha₀v⟩
            exact List.mem_filter.mpr ⟨hp₀, decide_eq_true hptrue⟩
        -- v x.val = sBlock-eval; and sBlock-eval ↔ p₀.2 x
        show v x.1 = p₀.2 x
        cases hvx : v x.1 with
        | true =>
            cases hsb : (sBlock ps x.1).eval v with
            | true => rw [hblock.mp hsb]
            | false =>
                rw [← hx] at hsb
                rw [hvx] at hsb
                exact absurd hsb (by simp)
        | false =>
            cases hsb : (sBlock ps x.1).eval v with
            | true =>
                rw [← hx] at hsb
                rw [hvx] at hsb
                exact absurd hsb (by simp)
            | false =>
                cases hp2 : p₀.2 x with
                | false => rfl
                | true => exact absurd (hblock.mpr hp2) (by rw [hsb]; simp)
      have hrestrict : restrictFill S v = p₀.2 := funext hw
      refine ⟨?_, ?_⟩
      · -- the t-definitions hold
        rw [eval_defsZip_ps_iff S v ps]
        intro q hq
        cases hvq : v q.1 with
        | true =>
            have hq1 : q.1 = p₀.1 := ha₀uniq q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩) hvq
            have hqp : q = p₀ := hpairFst q hq p₀ hp₀ hq1
            subst hqp
            rw [(eval_ZFormula_iff S q.2 v).mpr hrestrict]
        | false =>
            have hf : (ZFormula S q.2).eval v = false := by
              cases hz : (ZFormula S q.2).eval v with
              | false => rfl
              | true =>
                  have hrq : restrictFill S v = q.2 := (eval_ZFormula_iff S q.2 v).mp hz
                  have : q = p₀ := hpairSnd q hq p₀ hp₀ (hrestrict.symm.trans hrq).symm
                  subst this
                  rw [ha₀v] at hvq
                  exact absurd hvq (by simp [hz])
            rw [hf]
      · rw [← eval_restrictFill S X hsX v, hrestrict]
        exact (hcover p₀.2).mpr (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
  cases hL : (((defsZip (ps.map Prod.fst) (ps.map (fun p => ZFormula S p.2))).and X).eval v)
    <;> cases hR : (((sDefs ps).and (exactlyOne (ps.map Prod.fst))).eval v) <;>
    simp_all [key]

end Step3

/-! ### Assembly: Lemma 6 -/

section Lemma6

variable {S : Finset Atom} {A X : Formula Atom}

theorem support_sBlock_subset (ps : List (Atom × (↥S → Bool))) (a : Atom) :
    (sBlock ps a).support ⊆ (ps.map Prod.fst).toFinset := by
  unfold sBlock
  split
  · rename_i h
    intro x hx
    have hx2 := support_bigOr_subset _ hx
    rw [List.mem_toFinset] at hx2 ⊢
    obtain ⟨p, hpfilter, rfl⟩ := List.mem_map.mp hx2
    exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hpfilter).1, rfl⟩
  · exact Finset.empty_subset _

/-- **Lemma 6 (canonical reduction)**. Under its Requirements R1 and R2, the
plausibility of `(A | X)` equals that of the canonical problem: the query
"one of the favorable fresh symbols", against the premise "exactly one of the
fresh symbols". -/
theorem lemma6_canonical
    (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (ps : List (Atom × (↥S → Bool)))
    (hcover : ∀ w : ↥S → Bool, X.eval (fillTrue S w) = true ↔ w ∈ ps.map Prod.snd)
    (hpairSnd : ∀ p ∈ ps, ∀ q ∈ ps, p.2 = q.2 → p = q)
    (hpairFst : ∀ p ∈ ps, ∀ q ∈ ps, p.1 = q.1 → p = q)
    (htnodup : (ps.map Prod.fst).Nodup)
    (hfreshAX : ∀ s ∈ ps.map Prod.fst, s ∉ A.support ∪ X.support)
    (hfreshS : ∀ s ∈ ps.map Prod.fst, s ∉ S) :
    lp.value A X =
      lp.value (bigOr (ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map Prod.fst))
        (exactlyOne (ps.map Prod.fst)) := by
  set t := ps.map Prod.fst with ht
  set tA := ps.filter (fun p => A.eval (fillTrue S p.2) = true) |>.map Prod.fst with htA
  -- Step 1: add the t-definitions
  have h1 : lp.value A ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X)
      = lp.value A X := by
    refine r2_many_zip lp t (ps.map (fun p => ZFormula S p.2)) A X htnodup ?_ ?_
    · exact hfreshAX
    · intro s hs a ha z hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      exact fun hmem => hfreshS a ha (support_ZFormula_subset S q.2 hmem)
  -- Step 2: rewrite the query
  have h2 : lp.value A ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X)
      = lp.value (bigOr tA) ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X) := by
    refine value_congr_left lp A (bigOr tA) _ ?_
    intro v hv
    exact step2_eqvAt hsA hsX ps hcover v hv
  -- Step 3: transform the premise
  have h3 : lp.value (bigOr tA) ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X)
      = lp.value (bigOr tA) ((sDefs ps).and (exactlyOne t)) := by
    refine value_premise_eqv lp (bigOr tA) _ _ ?_
    intro v
    exact step3_premise_eqv hsA hsX ps hcover hpairSnd hpairFst htnodup v
  -- Step 4: drop the atom definitions
  have h4 : lp.value (bigOr tA) ((sDefs ps).and (exactlyOne t))
      = lp.value (bigOr tA) (exactlyOne t) := by
    refine r2_many_zip lp S.toList (S.toList.map (fun a => sBlock ps a)) (bigOr tA)
      (exactlyOne t) (Finset.nodup_toList S) ?_ ?_
    · intro s hs hmem
      have hSmem : s ∈ S := Finset.mem_toList.mp hs
      rcases Finset.mem_union.mp hmem with h1 | h2
      · have hsub := support_bigOr_subset tA h1
        rw [List.mem_toFinset] at hsub
        obtain ⟨q, hqfilter, rfl⟩ := List.mem_map.mp hsub
        exact hfreshS q.1 (List.mem_map.mpr ⟨q, (List.mem_filter.mp hqfilter).1, rfl⟩) hSmem
      · exact hfreshS s
          (List.mem_toFinset.mp (support_exactlyOne_subset t h2)) hSmem
    · intro s hs a ha z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact fun hmem => hfreshS a
        (List.mem_toFinset.mp (support_sBlock_subset ps b hmem))
        (Finset.mem_toList.mp ha)
  calc lp.value A X = lp.value A ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X) :=
        h1.symm
    _ = lp.value (bigOr tA) ((defsZip t (ps.map (fun p => ZFormula S p.2))).and X) := h2
    _ = lp.value (bigOr tA) ((sDefs ps).and (exactlyOne t)) := h3
    _ = lp.value (bigOr tA) (exactlyOne t) := h4

end Lemma6

/-! ### Slicing the enumeration -/

theorem filter_zip_take {α β : Type u} (dec : β → Bool) (t : List α)
    (ρAs ρNs : List β)
    (hlen : t.length = ρAs.length + ρNs.length)
    (hdecA : ∀ x ∈ ρAs, dec x = true) (hdecN : ∀ x ∈ ρNs, dec x = false) :
    ((t.zip (ρAs ++ ρNs)).filter (fun p => dec p.2)).map Prod.fst
      = t.take ρAs.length := by
  induction ρAs generalizing t with
  | nil =>
      simp only [List.nil_append, List.take]
      induction t generalizing ρNs with
      | nil => try rfl
      | cons x t ihT =>
          cases ρNs with
          | nil =>
              exfalso
              simp only [List.length_nil, List.length_cons] at hlen
              omega
          | cons y ρNs' =>
              have hlen' : t.length = ρNs'.length := by
                simp only [List.length_nil, List.length_cons] at hlen
                omega
              have ih2 := ihT ρNs' (fun x' hx' => hdecN x' (List.mem_cons_of_mem y hx'))
                (by simpa using hlen')
              have hdy : dec y = false := hdecN y List.mem_cons_self
              rw [List.zip_cons_cons, List.filter_cons_of_neg (by simp [hdy])]
              exact ih2
  | cons a ρAs ih =>
      cases t with
      | nil =>
          exfalso
          simp only [List.length_nil, List.length_cons] at hlen
          omega
      | cons x t' =>
          have hlen' : t'.length = ρAs.length + ρNs.length := by
            simp only [List.length_cons] at hlen
            omega
          have hda : dec a = true := hdecA a List.mem_cons_self
          show List.map Prod.fst (List.filter (fun p => dec p.2)
              ((x :: t').zip (a :: (ρAs ++ ρNs)))) = x :: t'.take ρAs.length
          rw [show (x :: t').zip (a :: (ρAs ++ ρNs))
              = (x, a) :: t'.zip (ρAs ++ ρNs) from rfl,
            List.filter_cons_of_pos (by simp [hda]), List.map_cons]
          rw [ih t' hlen' (fun x' hx' => hdecA x' (List.mem_cons_of_mem a hx'))]

/-! ### Zip injectivity -/

/-- Pairs of a zip over a duplicate-free first list are determined by their
first component. -/
theorem pair_eq_of_fst_eq_zip {α β : Type u} :
    ∀ (t : List α) (ρs : List β), t.Nodup →
    ∀ p q, p ∈ t.zip ρs → q ∈ t.zip ρs → p.1 = q.1 → p = q
  | [], _, _, _, _, hp, _, _ => absurd hp (by simp)
  | x :: t', ρs, hnodup, p, q, hp, hq, heq => by
      cases ρs with
      | nil => simp at hp
      | cons y ρs' =>
          rw [List.zip_cons_cons] at hp hq
          rcases List.mem_cons.mp hp with rfl | hp'
          · rcases List.mem_cons.mp hq with hq1 | hq'
            · exact hq1.symm
            · exfalso
              obtain ⟨hqF, _⟩ := List.of_mem_zip hq'
              have hqx : q.1 = x := heq.symm
              rw [hqx] at hqF
              exact (List.nodup_cons.mp hnodup).1 hqF
          · rcases List.mem_cons.mp hq with rfl | hq'
            · exfalso
              obtain ⟨hpF, _⟩ := List.of_mem_zip hp'
              have hpx : p.1 = x := heq
              rw [hpx] at hpF
              exact (List.nodup_cons.mp hnodup).1 hpF
            · exact pair_eq_of_fst_eq_zip t' ρs' (List.nodup_cons.mp hnodup).2
                p q hp' hq' heq

/-- Pairs of a zip over a duplicate-free second list are determined by their
second component. -/
theorem pair_eq_of_snd_eq_zip {α β : Type u} :
    ∀ (t : List α) (ρs : List β), ρs.Nodup →
    ∀ p q, p ∈ t.zip ρs → q ∈ t.zip ρs → p.2 = q.2 → p = q
  | _, [], _, _, _, hp, _, _ => absurd hp (by simp)
  | t, y :: ρs', hnodup, p, q, hp, hq, heq => by
      cases t with
      | nil => simp at hp
      | cons x t' =>
          rw [List.zip_cons_cons] at hp hq
          rcases List.mem_cons.mp hp with rfl | hp'
          · rcases List.mem_cons.mp hq with hq1 | hq'
            · exact hq1.symm
            · exfalso
              obtain ⟨_, hqS⟩ := List.of_mem_zip hq'
              have hqy : q.2 = y := heq.symm
              rw [hqy] at hqS
              exact (List.nodup_cons.mp hnodup).1 hqS
          · rcases List.mem_cons.mp hq with rfl | hq'
            · exfalso
              obtain ⟨_, hpS⟩ := List.of_mem_zip hp'
              have hpy : p.2 = y := heq
              rw [hpy] at hpS
              exact (List.nodup_cons.mp hnodup).1 hpS
            · exact pair_eq_of_snd_eq_zip t' ρs' (List.nodup_cons.mp hnodup).2
                p q hp' hq' heq

/-! ### Instantiation: plausibility depends only on the counts -/

section Counts

variable {S : Finset Atom} {A X : Formula Atom}

theorem modelsOn_and_eq (hsA : A.support ⊆ S) (hsX : X.support ⊆ S) :
    modelsOn S (A.and X) =
      (modelsOn S X).filter (fun w => A.eval (fillTrue S w) = true) := by
  ext w
  rw [mem_modelsOn_iff S (A.and X) (Finset.union_subset hsA hsX), Finset.mem_filter,
    mem_modelsOn_iff S X hsX]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact Bool.and_eq_true_iff.mpr ⟨h2, h1⟩

/-- **Corollary 8, syntactic form**. The plausibility of `(A | X)` is that of
the canonical problem with `m := #(A ∧ X)` favorable and `n := #X` cases,
counted over any finite support `S ⊇ σ(A, X)`. -/
theorem lemma6_counts (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (b : ℕ) (hb : (S ∪ (A.support ∪ X.support)).sup id < b) :
    lp.value A X =
      lp.value (bigOr ((freshAtoms b (modelsOn S X).card).take
          (modelsOn S (A.and X)).card))
        (exactlyOne (freshAtoms b (modelsOn S X).card)) := by
  set ρAs := ((modelsOn S X).filter (fun w => A.eval (fillTrue S w) = true)).toList with hρAs
  set ρNs := ((modelsOn S X).filter (fun w => A.eval (fillTrue S w) = false)).toList with hρNs
  set ρs := ρAs ++ ρNs with hρs
  set t := freshAtoms b ρs.length with ht
  -- lengths
  have hlenρAs : ρAs.length = (modelsOn S (A.and X)).card := by
    rw [hρAs, ← modelsOn_and_eq hsA hsX, Finset.length_toList]
  have hlenρs : ρs.length = (modelsOn S X).card := by
    have hcardT : ((modelsOn S X).filter (fun w => A.eval (fillTrue S w) = true)).card +
        ((modelsOn S X).filter (fun w => A.eval (fillTrue S w) = false)).card =
        (modelsOn S X).card := by
      have hpart : ((modelsOn S X).filter
          (fun w : ↥S → Bool => A.eval (fillTrue S w) = true)).card +
          ((modelsOn S X).filter (fun w : ↥S → Bool => ¬ A.eval (fillTrue S w) = true)).card
          = (modelsOn S X).card :=
        Finset.card_filter_add_card_filter_not _
      have hE : ((modelsOn S X).filter (fun w => A.eval (fillTrue S w) = false)) =
          ((modelsOn S X).filter (fun w => ¬ A.eval (fillTrue S w) = true)) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu, huA⟩; exact ⟨hu, by rw [huA]; simp⟩
        · rintro ⟨hu, huA⟩
          refine ⟨hu, ?_⟩
          cases hA : A.eval (fillTrue S u) with
          | true => exact absurd hA (by rw [hA] at huA; simp at huA)
          | false => rfl
      rw [hE]; exact hpart
    rw [hρs, List.length_append, hρAs, hρNs, Finset.length_toList, Finset.length_toList,
      hcardT]
  -- the enumeration covers exactly the models of X
  have hcover : ∀ w : ↥S → Bool, X.eval (fillTrue S w) = true ↔ w ∈ ρs := by
    intro w
    rw [hρs, hρAs, hρNs]
    constructor
    · intro hv
      have hwm : w ∈ modelsOn S X := by
        rw [mem_modelsOn_iff S X hsX]; exact hv
      cases hA : A.eval (fillTrue S w) with
      | true =>
          exact List.mem_append_left ρNs (Finset.mem_toList.mpr
            (Finset.mem_filter.mpr ⟨hwm, hA⟩))
      | false =>
          exact List.mem_append_right ρAs (Finset.mem_toList.mpr
            (Finset.mem_filter.mpr ⟨hwm, hA⟩))
    · intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · have h1 := Finset.mem_toList.mp hmem
        rw [Finset.mem_filter] at h1
        exact (mem_modelsOn_iff S X hsX w).mp h1.1
      · have h1 := Finset.mem_toList.mp hmem
        rw [Finset.mem_filter] at h1
        exact (mem_modelsOn_iff S X hsX w).mp h1.1
  -- pairwise properties
  have hnodupρs : ρs.Nodup := by
    rw [hρs]
    refine List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) ?_
    intro u hu1 hu2
    have h1 := Finset.mem_toList.mp hu1
    have h2 := Finset.mem_toList.mp hu2
    rw [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hnodupt : t.Nodup := freshAtoms_nodup b ρs.length
  have hzlen : t.length = ρs.length := by rw [ht, freshAtoms, List.length_map,
    List.length_range]
  have hps : (t.zip ρs).map Prod.fst = t := List.map_fst_zip (Nat.le_of_eq hzlen)
  have hpairFst : ∀ p ∈ t.zip ρs, ∀ q ∈ t.zip ρs, p.1 = q.1 → p = q :=
    fun p hp q hq heq => pair_eq_of_fst_eq_zip t ρs hnodupt p q hp hq heq
  have hpairSnd : ∀ p ∈ t.zip ρs, ∀ q ∈ t.zip ρs, p.2 = q.2 → p = q :=
    fun p hp q hq heq => pair_eq_of_snd_eq_zip t ρs hnodupρs p q hp hq heq
  -- freshness
  have hnotS : ∀ s ∈ t, s ∉ S := by
    intro s hs hS
    have h1 := le_of_mem_freshAtoms hs
    have h2 : s ≤ (S ∪ (A.support ∪ X.support)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left (A.support ∪ X.support) hS)
    exact Nat.lt_irrefl s (h2.trans_lt (hb.trans_le h1))
  have hfreshAX : ∀ s ∈ t, s ∉ A.support ∪ X.support := by
    intro s hs hmem
    have h1 := le_of_mem_freshAtoms hs
    rcases Finset.mem_union.mp hmem with hmem' | hmem'
    · have h2 : s ≤ (S ∪ (A.support ∪ X.support)).sup id :=
        Finset.le_sup (f := id)
          (Finset.mem_union_right S (Finset.mem_union_left X.support hmem'))
      exact Nat.lt_irrefl s (h2.trans_lt (hb.trans_le h1))
    · have h2 : s ≤ (S ∪ (A.support ∪ X.support)).sup id :=
        Finset.le_sup (f := id)
          (Finset.mem_union_right S (Finset.mem_union_right A.support hmem'))
      exact Nat.lt_irrefl s (h2.trans_lt (hb.trans_le h1))
  have hpsnd : (t.zip ρs).map Prod.snd = ρs :=
    List.map_snd_zip (Nat.le_of_eq hzlen.symm)
  -- the main reduction
  have hmain := lemma6_canonical lp hsA hsX (t.zip ρs)
    (fun w => by rw [hpsnd]; exact hcover w) hpairSnd hpairFst
    (by rw [hps]; exact hnodupt)
    (fun s hs => hfreshAX s (hps ▸ hs))
    (fun s hs => hnotS s (hps ▸ hs))
  -- convert the canonical query to the take-form
  have htake : ((t.zip ρs).filter (fun p => A.eval (fillTrue S p.2) = true)).map
      Prod.fst = t.take ρAs.length := by
    have hz := filter_zip_take (fun w => A.eval (fillTrue S w)) t ρAs ρNs
      (hzlen.trans (by rw [hρs, List.length_append]))
      (fun x hx => (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2)
      (fun x hx => (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2)
    have hfil2 : (t.zip ρs).filter (fun p => A.eval (fillTrue S p.2) = true) =
        (t.zip (ρAs ++ ρNs)).filter (fun p => A.eval (fillTrue S p.2)) := by
      rw [hρs]
      apply List.filter_congr
      intro p _
      simp
    rw [hfil2]
    exact hz
  -- assemble
  rw [hmain, htake, hps, ht, hρs, hlenρs, hlenρAs]

/-- **Van Horn's Corollary 8, syntactic form**: if `(A, X)` and `(B, Y)` have
the same numbers of favorable and total cases (over a common finite support),
then `(A | X) = (B | Y)`.  This is the bridge: with the semantic layer, it
says a `LogicalPlausibility`'s value depends only on the model counts. -/
theorem value_eq_of_counts_eq
    (S : Finset Atom) (A X B Y : Formula Atom)
    (hsA : A.support ⊆ S) (hsX : X.support ⊆ S)
    (hsB : B.support ⊆ S) (hsY : Y.support ⊆ S)
    (hm : (modelsOn S (A.and X)).card = (modelsOn S (B.and Y)).card)
    (hn : (modelsOn S X).card = (modelsOn S Y).card) :
    lp.value A X = lp.value B Y := by
  have hsub1 : S ∪ (A.support ∪ X.support) ⊆
      S ∪ ((A.support ∪ X.support) ∪ (B.support ∪ Y.support)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl h)))
  have hsub2 : S ∪ (B.support ∪ Y.support) ⊆
      S ∪ ((A.support ∪ X.support) ∪ (B.support ∪ Y.support)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr h)))
  set b := (S ∪ ((A.support ∪ X.support) ∪ (B.support ∪ Y.support))).sup id + 1 with hbdef
  have hsup : (S ∪ ((A.support ∪ X.support) ∪ (B.support ∪ Y.support))).sup id < b :=
    Nat.lt_succ_self _
  have h1 := lemma6_counts lp hsA hsX b
    (lt_of_le_of_lt (Finset.sup_mono (f := id) hsub1) hsup)
  have h2 := lemma6_counts lp hsB hsY b
    (lt_of_le_of_lt (Finset.sup_mono (f := id) hsub2) hsup)
  rw [h1, h2, hm, hn]

end Counts

end Plausibility
