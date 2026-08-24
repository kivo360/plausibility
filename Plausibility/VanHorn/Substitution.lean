/-
Substitution and change-of-variables infrastructure for the syntactic layer:
atom supports, lifting formulas along atom maps (fresh symbols via `Option`,
disjoint vocabularies via `Sum`), the semantic content of defining a fresh
symbol (R2), and the diagram formula that isolates a single truth assignment
(Lemma 6's `Z_i`).
-/

import Plausibility.PropLogic.Semantics

namespace Plausibility

universe u v

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {α β : Type u}

namespace Formula

/-- Lift a formula along an atom map `f`. -/
def mapLift (f : α → β) : Formula α → Formula β
  | .atom a => .atom (f a)
  | .bot => .bot
  | .neg p => .neg (p.mapLift f)
  | .and p q => .and (p.mapLift f) (q.mapLift f)

/-- The atoms occurring in a formula. -/
noncomputable def support [DecidableEq α] : Formula α → Finset α
  | .atom a => {a}
  | .bot => ∅
  | .neg p => p.support
  | .and p q => p.support ∪ q.support

theorem eval_mapLift (f : α → β) (w : β → Bool) :
    ∀ φ : Formula α, (φ.mapLift f).eval w = φ.eval (w ∘ f)
  | .atom _ => rfl
  | .bot => rfl
  | .neg p => by simp [mapLift, eval, eval_mapLift f w p]
  | .and p q => by simp [mapLift, eval, eval_mapLift f w p, eval_mapLift f w q]

end Formula

open Formula

/-! ### Fresh symbols via `Option` (R2) -/

/-- The formula `(s ↔ E)` defining the fresh symbol `s := none` as `E`. -/
def defFormula (E : Formula α) : Formula (Option α) :=
  (Formula.atom none).iff (E.mapLift some)

/-- The valuation on `Option α` obtained from `v' : α → Bool` by defining
`none` according to `E`. -/
def defineVal (E : Formula α) (v' : α → Bool) : Option α → Bool :=
  fun o => o.elim (E.eval v') v'

theorem eval_lift_defineVal (E : Formula α) (v' : α → Bool) (φ : Formula α) :
    (φ.mapLift some).eval (defineVal E v') = φ.eval v' := by
  rw [eval_mapLift some]
  rfl

theorem eval_defFormula (w : Option α → Bool) (E : Formula α) :
    (defFormula E).eval w = (w none == E.eval (w ∘ some)) := by
  simp only [defFormula, Formula.iff, Formula.imp, Formula.eval, eval_mapLift some]
  cases w none <;> cases E.eval (w ∘ some) <;> rfl

/-- **Semantic content of R2.** Defining a fresh symbol sets up a bijection
between the satisfying assignments of `(s ↔ E) ∧ lift X` and those of `X`. -/
noncomputable def r2Equiv [Fintype α] [DecidableEq α] (E X : Formula α) :
    {w : Option α → Bool // w ∈ models ((defFormula E).and (X.mapLift some))} ≃
      {v' : α → Bool // v' ∈ models X} where
  toFun w := ⟨w.1 ∘ some, by
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (mem_models_iff.mp w.2)
    rw [mem_models_iff]
    have hX : (X.mapLift some).eval w.1 = X.eval (w.1 ∘ some) :=
      eval_mapLift some w.1 X
    exact hX ▸ h2⟩
  invFun v' := ⟨defineVal E v'.1, by
    have hX : X.eval v'.1 = true := mem_models_iff.mp v'.2
    rw [mem_models_iff, Formula.eval, eval_defFormula, eval_lift_defineVal, hX]
    simp
    rw [← eval_mapLift some, eval_lift_defineVal]
    rfl⟩
  left_inv w := by
    apply Subtype.ext
    funext o
    match o with
    | none =>
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (mem_models_iff.mp w.2)
      rw [eval_defFormula, beq_iff_eq] at h1
      show E.eval (w.1 ∘ some) = w.1 none
      exact h1.symm
    | some a => rfl
  right_inv v' := by
    apply Subtype.ext
    funext a
    rfl

/-! ### Disjoint vocabularies via `Sum` (R3) -/

/-- **Semantic content of R3.** Conjoining a formula over a disjoint
vocabulary splits the satisfying assignments into a product. -/
noncomputable def sumEquiv [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (X : Formula α) (Y : Formula β) :
    {w : Sum α β → Bool // w ∈ models ((X.mapLift Sum.inl).and (Y.mapLift Sum.inr))} ≃
      {p : (α → Bool) × (β → Bool) // p ∈ (models X) ×ˢ (models Y)} where
  toFun w := ⟨(w.1 ∘ Sum.inl, w.1 ∘ Sum.inr), by
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (mem_models_iff.mp w.2)
    rw [Finset.mem_product, mem_models_iff, mem_models_iff]
    exact ⟨by rwa [← eval_mapLift Sum.inl w.1 X], by rwa [← eval_mapLift Sum.inr w.1 Y]⟩⟩
  invFun p := ⟨Sum.elim p.1.1 p.1.2, by
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp p.2
    rw [mem_models_iff, Formula.eval, eval_mapLift Sum.inl _ X, eval_mapLift Sum.inr _ Y]
    rw [show Sum.elim p.1.1 p.1.2 ∘ Sum.inl = p.1.1 from rfl,
        show Sum.elim p.1.1 p.1.2 ∘ Sum.inr = p.1.2 from rfl]
    rw [mem_models_iff.mp h1, mem_models_iff.mp h2]
    rfl⟩
  left_inv w := by
    apply Subtype.ext
    funext o
    match o with
    | .inl a => rfl
    | .inr b => rfl
  right_inv p := by
    apply Subtype.ext
    rfl

theorem card_models_def_and [Fintype α] [DecidableEq α] (E X : Formula α) :
    (models ((defFormula E).and (X.mapLift some))).card = (models X).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (r2Equiv E X), Fintype.card_coe]

theorem card_models_sum [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (X : Formula α) (Y : Formula β) :
    (models ((X.mapLift Sum.inl).and (Y.mapLift Sum.inr))).card =
      (models X).card * (models Y).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (sumEquiv X Y), Fintype.card_coe,
    Finset.card_product]

/-! ### The diagram formula (Lemma 6's `Z_i`) -/

/-- The literal on atom `a` that is true exactly under `v`. -/
def diagramLit (v : α → Bool) (a : α) : Formula α :=
  if v a then Formula.atom a else Formula.neg (Formula.atom a)

/-- The diagram (complete conjunction) of a truth assignment: satisfied by
exactly that one assignment. -/
noncomputable def diagram [Fintype α] [DecidableEq α] (v : α → Bool) : Formula α :=
  Finset.univ.toList.foldr (fun a acc => (diagramLit v a).and acc) Formula.top

private theorem eval_foldr_and (w : α → Bool) (f : α → Formula α) (l : List α) :
    (l.foldr (fun a acc => (f a).and acc) Formula.top).eval w = true ↔
      ∀ a ∈ l, (f a).eval w = true := by
  induction l with
  | nil => simp [Formula.top, Formula.eval]
  | cons a l ih =>
      rw [List.foldr_cons, Formula.eval, Bool.and_eq_true_iff, ih,
        List.forall_mem_cons]

theorem eval_diagram [Fintype α] [DecidableEq α] (v w : α → Bool) :
    (diagram v).eval w = true ↔ w = v := by
  rw [diagram, eval_foldr_and]
  constructor
  · intro hall
    funext a
    have hv : (diagramLit v a).eval w = true :=
      hall a (Finset.mem_toList.2 (Finset.mem_univ a))
    unfold diagramLit at hv
    by_cases hva : v a
    · rw [if_pos hva, Formula.eval] at hv
      simpa [hva] using hv
    · rw [if_neg hva, Formula.eval, Formula.eval] at hv
      simp only [Bool.not_eq_true'] at hv
      simpa [hva] using hv
  · intro h a _
    subst h
    unfold diagramLit
    split <;> simp_all [Formula.eval]

theorem models_diagram [Fintype α] [DecidableEq α] (v : α → Bool) :
    models (diagram v) = {v} := by
  ext w
  rw [mem_models_iff, eval_diagram]
  simp

end Plausibility
