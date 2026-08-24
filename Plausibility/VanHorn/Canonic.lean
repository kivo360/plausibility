/-
Canonical reduction over a single global atom language `Atom := ℕ`.
List-level formula combinators (`bigOr`, `allNeg`, `exactlyOne`, `defsList`),
their evaluation lemmas, a model-counting interface over a finite support set
(`modelsOn`), and the support-subset cardinality theorem needed by Van Horn's
Lemma 6.
-/

import Plausibility.VanHorn.Requirements
import Mathlib.Tactic

namespace Plausibility

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Formula

private theorem eval_or_iff (p q : Formula Atom) (v : Atom → Bool) :
    (p.or q).eval v = true ↔ (p.eval v = true ∨ q.eval v = true) := by
  unfold Formula.or
  simp [Formula.eval]

private theorem eval_and_iff (p q : Formula Atom) (v : Atom → Bool) :
    (p.and q).eval v = true ↔ (p.eval v = true ∧ q.eval v = true) := by
  simp [Formula.eval]

private theorem eval_neg_iff (p : Formula Atom) (v : Atom → Bool) :
    (p.neg).eval v = true ↔ p.eval v = false := by
  simp [Formula.eval]

private theorem eval_atom_iff (a : Atom) (v : Atom → Bool) :
    (Formula.atom a).eval v = true ↔ v a = true := by rfl

private theorem eval_atom_false_iff (a : Atom) (v : Atom → Bool) :
    (Formula.atom a).eval v = false ↔ v a = false := by rfl

/-! ### List-level combinators -/

/-- The disjunction of the atoms in a list. -/
def bigOr (l : List Atom) : Formula Atom :=
  l.foldr (fun a acc => Formula.or (Formula.atom a) acc) Formula.bot

theorem eval_bigOr_iff (v : Atom → Bool) (l : List Atom) :
    (bigOr l).eval v = true ↔ ∃ a ∈ l, v a = true := by
  induction l with
  | nil => simp [bigOr, Formula.eval]
  | cons a l ih =>
      rw [bigOr, List.foldr_cons, eval_or_iff, eval_atom_iff]
      constructor
      · rintro (h | h)
        · exact ⟨a, by simp, h⟩
        · rcases ih.mp h with ⟨b, hb, hvb⟩
          exact ⟨b, by simp [hb], hvb⟩
      · rintro ⟨b, hb, hvb⟩
        simp at hb
        rcases hb with rfl | hb
        · exact Or.inl hvb
        · exact Or.inr (ih.mpr ⟨b, hb, hvb⟩)

/-- The conjunction of the negations of all atoms in a list. -/
def allNeg (l : List Atom) : Formula Atom :=
  l.foldr (fun a φ => (Formula.atom a).neg.and φ) Formula.top

theorem eval_allNeg_iff (v : Atom → Bool) (l : List Atom) :
    (allNeg l).eval v = true ↔ ∀ a ∈ l, v a = false := by
  induction l with
  | nil => simp [allNeg, Formula.top, Formula.eval]
  | cons a l ih =>
      rw [allNeg, List.foldr_cons, eval_and_iff, eval_neg_iff, eval_atom_false_iff]
      constructor
      · rintro ⟨h, hall⟩
        intro b hb
        simp at hb
        rcases hb with rfl | hb
        · exact h
        · exact (ih.mp hall) b hb
      · intro hall
        constructor
        · exact hall a (by simp)
        · exact ih.mpr (fun b hb => hall b (by simp [hb]))

/-- Exactly one of the atoms in `l` is true.  Requires `l` to have no
duplicates for the evaluation lemma to hold. -/
def exactlyOne : List Atom → Formula Atom
  | [] => Formula.bot
  | b :: l => ((Formula.atom b).and (allNeg l)).or
                ((Formula.atom b).neg.and (exactlyOne l))

theorem eval_exactlyOne_iff (v : Atom → Bool) (l : List Atom) (hn : l.Nodup) :
    (exactlyOne l).eval v = true ↔
      ∃ a, a ∈ l ∧ v a = true ∧ ∀ a' ∈ l, v a' = true → a' = a := by
  induction l with
  | nil =>
      simp [exactlyOne, Formula.eval]
  | cons b l ih =>
      have hn' : l.Nodup := (List.nodup_cons.mp hn).2
      have hnotin : b ∉ l := (List.nodup_cons.mp hn).1
      rw [exactlyOne, eval_or_iff]
      simp only [eval_and_iff, eval_neg_iff, eval_atom_iff, eval_atom_false_iff,
        eval_allNeg_iff, ih hn']
      cases hvb : v b with
      | true =>
          simp [hvb, hnotin]
          constructor
          · intro hall a1 ha1 hva1
            exfalso
            have hf : v a1 = false := hall a1 ha1
            rw [hva1] at hf
            simp at hf
          · intro huniq a1 ha1
            by_contra h
            have hv1 : v a1 = true := by
              cases hv : v a1 <;> simp_all
            have haa : a1 = b := huniq a1 ha1 hv1
            subst a1
            exact hnotin ha1
      | false =>
          simp [hvb]

/-- The conjunction of the equivalences `(s ↔ Es s)` over a list of atoms. -/
def defsList (l : List Atom) (Es : Atom → Formula Atom) : Formula Atom :=
  (l.map (fun s => (Formula.atom s).iff (Es s))).foldr Formula.and Formula.top

/-! ### Support of `defsList` -/

/-- The support of an iff is contained in the union of the supports. -/
theorem support_iff (p q : Formula Atom) :
    (p.iff q).support ⊆ p.support ∪ q.support := by
  intro a ha
  simp only [Formula.iff, Formula.imp, Formula.support, Finset.mem_union] at ha
  simp only [Finset.mem_union]
  tauto

/-- The support of an or is contained in the union of the supports. -/
theorem support_or (p q : Formula Atom) :
    (p.or q).support ⊆ p.support ∪ q.support := by
  intro a ha
  simp only [Formula.or, Formula.support, Finset.mem_union] at ha
  simp only [Finset.mem_union]
  tauto

/-- The support of an implication is contained in the union of the supports. -/
theorem support_imp (p q : Formula Atom) :
    (p.imp q).support ⊆ p.support ∪ q.support := by
  intro a ha
  simp only [Formula.imp, Formula.support, Finset.mem_union] at ha
  simp only [Finset.mem_union]
  tauto

theorem support_defsList (l : List Atom) (Es : Atom → Formula Atom) :
    (defsList l Es).support ⊆ l.toFinset ∪ ((l.map Es).foldr (fun φ acc => φ.support ∪ acc) ∅) := by
  induction l with
  | nil =>
      simp [defsList, Formula.support, Formula.top]
  | cons s l ih =>
      intro a ha
      simp only [defsList, List.map_cons, List.foldr_cons, Formula.support, Finset.mem_union] at ha ⊢
      have hs : ((Formula.atom s).iff (Es s)).support ⊆
          (Formula.atom s).support ∪ (Es s).support := support_iff _ _
      rcases ha with hsl | hrl
      · rcases (Finset.mem_union.mp (hs hsl)) with hsa | hes
        · left
          simp only [Formula.support] at hsa
          simp only [List.toFinset_cons, Finset.mem_insert]
          exact Or.inl (by simpa [Formula.support] using hsa)
        · right
          exact Or.inl hes
      · have hih := ih hrl
        rcases (Finset.mem_union.mp hih) with h1 | h2
        · left
          simp only [List.toFinset_cons, Finset.mem_insert]
          exact Or.inr h1
        · right
          exact Or.inr h2

/-! ### Congruence of evaluation under equal valuations -/

/-- If two valuations agree on the support of `φ`, they evaluate `φ` equally. -/
theorem eval_congr : ∀ {φ : Formula Atom} {v w : Atom → Bool},
    (∀ a ∈ φ.support, v a = w a) → φ.eval v = φ.eval w := by
  intro φ
  induction φ with
  | atom a =>
      intro v w h
      have hv : v a = w a := h a (by simp [Formula.support])
      simp [Formula.eval, hv]
  | bot =>
      intro v w h
      rfl
  | neg p ih =>
      intro v w h
      simp only [Formula.eval]
      congr 1
      exact ih (by intro a ha; exact h a (by simp [Formula.support] at ha ⊢; exact ha))
  | and p q ihp ihq =>
      intro v w h
      simp only [Formula.eval]
      congr 1
      · exact ihp (by intro a ha; exact h a (by simp [Formula.support]; exact Or.inl ha))
      · exact ihq (by intro a ha; exact h a (by simp [Formula.support]; exact Or.inr ha))

/-! ### Models over a finite support set -/

/-- Extend a valuation on a subset `S` to all atoms by filling in `true`. -/
def fillTrue (S : Finset Atom) (w : {x // x ∈ S} → Bool) : Atom → Bool :=
  fun a => if h : a ∈ S then w ⟨a, h⟩ else true

/-- Restrict a total valuation to the subtype of atoms in `S`. -/
def restrictFill (S : Finset Atom) (v : Atom → Bool) : {x // x ∈ S} → Bool :=
  fun x => v x.val

/-- The set of valuations on `S` whose extension satisfies `φ`. -/
def modelsOn (S : Finset Atom) (φ : Formula Atom) : Finset ({x // x ∈ S} → Bool) :=
  Finset.univ.filter fun w => φ.eval (fillTrue S w) = true

theorem mem_modelsOn_iff (S : Finset Atom) (φ : Formula Atom)
    (_hs : φ.support ⊆ S) (w : {x // x ∈ S} → Bool) :
    w ∈ modelsOn S φ ↔ φ.eval (fillTrue S w) = true := by
  simp [modelsOn]

theorem eval_restrictFill (S : Finset Atom) (φ : Formula Atom)
    (hs : φ.support ⊆ S) (v : Atom → Bool) :
    φ.eval (fillTrue S (restrictFill S v)) = φ.eval v := by
  apply eval_congr
  intro a ha
  have haS : a ∈ S := hs ha
  simp [fillTrue, restrictFill, haS]

theorem modelsOn_mem_of_eval (S : Finset Atom) (φ : Formula Atom)
    (hs : φ.support ⊆ S) (v : Atom → Bool) (hv : φ.eval v = true) :
    restrictFill S v ∈ modelsOn S φ := by
  rw [mem_modelsOn_iff S φ hs]
  rw [eval_restrictFill S φ hs v]
  exact hv

theorem eval_of_modelsOn_mem (S : Finset Atom) (φ : Formula Atom)
    (hs : φ.support ⊆ S) (w : {x // x ∈ S} → Bool)
    (hw : w ∈ modelsOn S φ) : φ.eval (fillTrue S w) = true := by
  exact (mem_modelsOn_iff S φ hs w).mp hw

/-! ### Cardinality over nested supports -/

/-- Restriction map from valuations on `T` to valuations on a subset `S ⊆ T`. -/
def restrictOn {S T : Finset Atom} (h : S ⊆ T)
    (w : {x // x ∈ T} → Bool) : {x // x ∈ S} → Bool :=
  fun y => w ⟨y.1, h y.2⟩

/-- A `T`-valuation restricts to an `S`-model iff the `T`-valuation is an
`S`-extended model, whenever `φ.support ⊆ S ⊆ T`. -/
theorem restrictOn_mem_modelsOn {S T : Finset Atom} (φ : Formula Atom)
    (hS : φ.support ⊆ S) (hST : S ⊆ T) (w : {x // x ∈ T} → Bool) :
    restrictOn hST w ∈ modelsOn S φ ↔ w ∈ modelsOn T φ := by
  rw [mem_modelsOn_iff T φ (by intro a ha; exact hST (hS ha)) w]
  rw [mem_modelsOn_iff S φ hS (restrictOn hST w)]
  have heq : φ.eval (fillTrue T w) = φ.eval (fillTrue S (restrictOn hST w)) := by
    apply eval_congr
    intro a ha
    have haS : a ∈ S := hS ha
    have haT : a ∈ T := hST haS
    simp [fillTrue, restrictOn, haS, haT]
  rw [heq]

/-- Split a `T`-valuation index into an `S`-index or a `(T \ S)`-index. -/
def sumSplit {S T : Finset Atom} (_h : S ⊆ T) (y : {a // a ∈ T}) :
    {a // a ∈ S} ⊕ {a // a ∈ T \ S} :=
  if hy : y.1 ∈ S then Sum.inl ⟨y.1, hy⟩ else Sum.inr ⟨y.1, by
    rw [Finset.mem_sdiff]
    exact ⟨y.2, hy⟩⟩

/-- The inverse of `sumSplit`. -/
def sumJoin {S T : Finset Atom} (h : S ⊆ T) :
    ({a // a ∈ S} ⊕ {a // a ∈ T \ S}) → {a // a ∈ T} :=
  fun z => z.elim (fun a => ⟨a.1, h a.2⟩) (fun b => ⟨b.1, (Finset.mem_sdiff.mp b.2).1⟩)

/-- `↥T ≃ ↥S ⊕ ↥(T \ S)` when `S ⊆ T`. -/
noncomputable def sum_split_equiv {S T : Finset Atom} (h : S ⊆ T) :
    ({a // a ∈ T} ≃ ({a // a ∈ S} ⊕ {a // a ∈ T \ S})) :=
  { toFun := sumSplit h
    invFun := sumJoin h
    left_inv := by
      intro y
      by_cases hy : y.1 ∈ S
      · simp [sumSplit, sumJoin, hy]
      · simp [sumSplit, sumJoin, hy]
    right_inv := by
      intro z
      cases z with
      | inl a =>
          by_cases hmem : a.1 ∈ S
          · simp [sumSplit, sumJoin, hmem]
          · exfalso; exact hmem a.2
      | inr b =>
          have hbS : b.1 ∉ S := (Finset.mem_sdiff.mp b.2).2
          simp [sumSplit, sumJoin, hbS] }

/-- A `T`-valuation splits into its `S`-part and its `(T \ S)`-part. -/
noncomputable def splitFun {S T : Finset Atom} (h : S ⊆ T) :
    ({x // x ∈ T} → Bool) ≃
      (({x // x ∈ S} → Bool) × ({x // x ∈ T \ S} → Bool)) :=
  (Equiv.piCongrLeft (fun _ : ({a // a ∈ S} ⊕ {a // a ∈ T \ S}) => Bool) (sum_split_equiv h)).trans
      (Equiv.sumArrowEquivProdArrow ({a // a ∈ S}) ({a // a ∈ T \ S}) Bool)

/-- The `S`-part of a split `T`-valuation is its restriction to `S`. -/
theorem splitFun_fst {S T : Finset Atom} (h : S ⊆ T) (w : {x // x ∈ T} → Bool) :
    (splitFun h w).1 = restrictOn h w := by
  funext y
  simp only [splitFun, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.piCongrLeft_apply, restrictOn]
  have harg : (sum_split_equiv h).symm (Sum.inl y) = ⟨y.1, h y.2⟩ := by rfl
  rw [← harg]
  simp

/-- Membership in `modelsOn T φ` depends only on the restriction to `S`,
whenever `φ.support ⊆ S ⊆ T`. -/
theorem restrictOn_mem_iff {S T : Finset Atom} (φ : Formula Atom)
    (hS : φ.support ⊆ S) (hT : φ.support ⊆ T) (h : S ⊆ T)
    (w : {x // x ∈ T} → Bool) :
    w ∈ modelsOn T φ ↔ restrictOn h w ∈ modelsOn S φ := by
  rw [mem_modelsOn_iff T φ hT w]
  rw [mem_modelsOn_iff S φ hS]
  have heq : φ.eval (fillTrue T w) = φ.eval (fillTrue S (restrictOn h w)) := by
    apply eval_congr
    intro a ha
    have haS : a ∈ S := hS ha
    have haT : a ∈ T := h haS
    simp [fillTrue, restrictOn, haS, haT]
  rw [heq]

/-- `{_b : B // True} ≃ B`. -/
def subtypeTrue (B : Type) : {_b : B // True} ≃ B :=
  { toFun := fun b => b.1
    invFun := fun b => ⟨b, True.intro⟩
    left_inv := by intro _b; apply Subtype.ext; rfl
    right_inv := by intro _b; rfl }

/-- **Cardinality over nested supports.** Adding the atoms `T \ S` outside the
support of `φ` multiplies the model count by `2 ^ (T \ S).card`.  A
`T`-valuation splits as an `S`-part (which decides membership in `modelsOn`,
since `φ.support ⊆ S`) and a free `(T \ S)`-part. -/
theorem card_modelsOn_subset (S T : Finset Atom) (φ : Formula Atom)
    (hS : φ.support ⊆ S) (hT : φ.support ⊆ T) (h : S ⊆ T) :
    (modelsOn S φ).card * 2 ^ (T \ S).card = (modelsOn T φ).card := by
  let A := {x // x ∈ S} → Bool
  let B := {x // x ∈ T \ S} → Bool
  have hmem (w : {x // x ∈ T} → Bool) :
      w ∈ modelsOn T φ ↔ (splitFun h w).1 ∈ modelsOn S φ := by
    rw [splitFun_fst h w]
    exact restrictOn_mem_iff φ hS hT h w
  have e1 : {w // w ∈ modelsOn T φ} ≃ {p : A × B // p.1 ∈ modelsOn S φ} :=
    (splitFun h).subtypeEquiv hmem
  have e2 : {p : A × B // p.1 ∈ modelsOn S φ} ≃ ↥(modelsOn S φ) × B :=
    { toFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      invFun := fun q => ⟨(q.1.1, q.2), q.1.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro q; ext <;> rfl }
  have hcard : (modelsOn T φ).card = (modelsOn S φ).card * Fintype.card B := by
    rw [← Fintype.card_coe (modelsOn T φ)]
    rw [Fintype.card_congr (e1.trans e2)]
    simp [Fintype.card_prod]
  have hB : Fintype.card B = 2 ^ (T \ S).card := by
    dsimp [B]
    rw [Fintype.card_fun]
    rw [Fintype.card_coe]
    simp [Fintype.card_bool]
  rw [hcard]
  rw [hB]

end Plausibility
