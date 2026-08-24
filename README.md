# Plausibility — Lean formalization of Van Horn's uniqueness theorem

A Lean 4 + Mathlib formalization of Kevin S. Van Horn,
*From propositional logic to plausible reasoning: A uniqueness theorem*,
International Journal of Approximate Reasoning 88 (2017) 309–332.

## Build

```bash
lake build        # requires the pinned toolchain (lean-toolchain) and Mathlib
```

The first build fetches prebuilt Mathlib oleans:

```bash
lake exe cache get
lake build
```

## Status

**COMPLETE. The paper's core theorem is machine-verified end-to-end, from the
raw Requirements R1–R4 to rational probability.** The semantic finite-event
layer (Theorems 14 and 16, Corollaries 8, 12, 15), the syntactic bridge from
R1+R2 to count dependence (Lemma 6 / Corollary 8, in `Reduction.lean`), and the
R3/R4 transfer (in `Bridge.lean`): `toSystem : LogicalPlausibility P →
PlausibilitySystem P` with all three structural fields, and the final
calibration theorem `vanHorn_calibration` — `lp.value A X = Υ₁ (toSystem lp)
(#(A∧X) / #X)` — are all proved, with no `sorry` and no axioms beyond the
standard three. Every theorem in the project passes `#print axioms` with
`[propext, Classical.choice, Quot.sound]` only.

## What is proved

The project is layered exactly as the paper's argument runs:

```
Propositional problem (A | X)                 [PropLogic/, VanHorn/Requirements.lean]
          ↓  R1 + R2, Lemma 6 — PROVED syntactically  [VanHorn/Reduction.lean]
Finite event with m favorable worlds out of n  [Basic.lean, Canonical.lean]
          ↓  R3 (irrelevant information)        [ScaleInvariant.lean]
Only the ratio m/n matters                     [RationalRepresentation.lean]
          ↓  R4 (strict ordering)
Plausibility order ≅ rational [0,1]            [ProbabilityTheorem.lean]
```

### Semantic finite-event layer (fully proved)

* `PlausibilitySystem P` — a plausibility score on events of *every* finite,
  nonempty world space, valued in a **partial** order `P`, subject to the
  semantic analogues of the requirements:
  * `equiv_invariance` — invariance under bijection of world spaces
    (semantic consequence of R1 + R2, cf. Definition 5 / Corollary 9),
  * `irrelevant_product` — R3: product with an independent space is
    plausibility-preserving,
  * `strict_mono` — R4: strict subsets are strictly less plausible.
* `eventEquiv_canonical` / `score_eq_canonical` — **Lemma 6 / Corollary 8**:
  every event scores exactly like the canonical `m`-of-`n` problem.
* `upsilon₂_scale` — **Lemma 10**: `(m, n)` and `(k·m, k·n)` have equal
  plausibility; only the ratio `m/n` matters.
* `upsilon₂_eq_of_rat_eq` — equal rational ratios give equal plausibilities
  (well-definedness of `Υ₁ : Rat01 → P`).
* `upsilon₁_strictMono` — **Lemma 13**: strictly larger rational probability
  means strictly larger plausibility.
* `score_eq_iff_probability_eq`, `score_lt_iff_probability_lt` — the
  iff-forms of Corollary 12.
* `score_eq_upsilon₁` — **Theorem 14 (representation)**: `score A =
  upsilon₁ (↑#A / ↑#Ω)`.
* `plausibilityOrderIso` — **Theorem 14 (isomorphism)**: the *achieved*
  plausibility values (`PlausibilityRange sys`, ranging over world spaces of
  all finite sizes) are order-isomorphic to `Rat01 = ℚ ∩ [0,1]`.  `P` is only
  assumed partially ordered; linearity of the achieved values is derived.
* `countSystem` — **Theorem 16 (consistency)**: the counting measure
  `score A := #A / #Ω` in `ℚ` satisfies all three structural fields, so the
  requirements are jointly satisfiable and the theorem is not vacuous.

### Syntactic layer (fully proved)

* `PropLogic/Formula.lean` — syntax (`atom`, `bot`, `neg`, `and`, derived
  `or`/`imp`/`iff`/`top`) and Boolean evaluation.
* `PropLogic/Semantics.lean` — `models φ` as a `Finset (α → Bool)`,
  `Satisfiable`, `logicalProbability A X = #(A ∧ X) / #X` with
  `0 ≤ · ≤ 1`, plus four `native_decide` exhaustive-enumeration sanity checks.
* `VanHorn/Requirements.lean` — the raw syntactic requirements
  `LogicalPlausibility P` over `Atom := ℕ`: R1 (equivalence), R2 (fresh
  definitions), R3 (irrelevant fresh vocabulary), R4 (strict entailment), each
  as an explicit structure field.
* `VanHorn/Substitution.lean` — the semantic content of R2/R3: definitions
  preserve models (`r2Equiv`, `card_models_def_and`), vocabularies split as
  products (`sumEquiv`, `card_models_sum`), and the diagram `Z_i` isolating a
  single assignment (`diagram`, `models_diagram`).
* `VanHorn/Reduction.lean` — **Lemma 6, fully proved from R1+R2**:
  * iterated R2 (`r2_many`, `r2_many_zip`),
  * step 2: query becomes a disjunction of favorable symbols
    (`step2_eqvAt`),
  * step 3: premise becomes exactly-one (`step3_premise_eqv`),
  * the four-step reduction (`lemma6_canonical`),
  * **Corollary 8 (syntactic)**: `lemma6_counts`, `value_eq_of_counts_eq` —
    `lp.value A X` depends only on `(#(A∧X), #X)`.
* `VanHorn/Canonic.lean` — canonical formula machinery (`bigOr`,
  `exactlyOne`, `allNeg`), `modelsOn`, `card_modelsOn_subset`, and the
  model-counting lemmas (`card_modelsOn_exactlyOne`, `card_modelsOn_split`,
  `card_modelsOn_bigOr_and_exactlyOne`).
* `VanHorn/ProbabilityLaws.lean` — **Corollary 15**: complement and product
  rules for the counting measure, plus the unsatisfiable-premise convention
  (`extendedProbability`).
* `VanHorn/Counterexamples.lean` — **R4 is not derivable from R1–R3**:
  `threeSystem` satisfies `equiv_invariance` and `irrelevant_product` but
  violates `strict_mono`; plus a nonuniform example (`biased_coin_heads`).

### Bridge to propositional problems (complete)

* `eventOf` / `score_eventOf` — for a satisfiable premise `X`, scoring the
  event of `X`-worlds satisfying `A` equals the plausibility of the logical
  probability `#models(A ∧ X) / #models X`.
* `VanHorn/Bridge.lean` — the R3/R4 transfer:
  * `value_scale` — syntactic scale invariance (Lemma 10 at the formula
    level, via R3 with shared fresh atoms),
  * `value_mono_canonical` — canonical strict monotonicity (via R4),
  * `toSystem : LogicalPlausibility P → PlausibilitySystem P` — the
    instance, with `equiv_invariance`, `irrelevant_product`, `strict_mono`
    all proved (compiles),
  * `vanHorn_calibration` — **the final calibration theorem**: `lp.value A X
    = Υ₁ (toSystem lp) (probOf (event of A-worlds within X-worlds))`. Together
    with `score_eq_upsilon₁` and `plausibilityOrderIso`, Van Horn's Theorem 14
    now applies verbatim to the raw Requirements.
* `Sanity` section — `(1,2) = (2,4)` in plausibility (Lemma 10) and
  `(1,3) < (1,2)` (Lemma 13), for *every* plausibility system.

## Honest scope statement

The paper's **finite uniqueness theorem** is fully machine-checked end-to-end:
the semantic layer, the syntactic Lemma-6 bridge from raw R1+R2, and the R3/R4
transfer to the `PlausibilitySystem` instance with the final calibration
theorem. The measure-theoretic extension to infinite domains (paper §9.3) is
out of scope. Unsatisfiable premises are excluded from the main theorems, as in
the paper.

Axiom check: every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound` (verified via `#print axioms`); no `sorry` or custom axioms.
R1–R4 enter as explicit structure fields, not global axioms.

## File tree

```
Plausibility.lean
Plausibility/Basic.lean                  -- EventEquiv, PlausibilitySystem
Plausibility/Canonical.lean              -- canonical events, Corollary 8
Plausibility/ScaleInvariant.lean         -- Lemma 10 (scale invariance)
Plausibility/RationalRepresentation.lean -- upsilon₁, Lemma 13
Plausibility/ProbabilityTheorem.lean     -- Theorem 14, 16, iff-forms, bridge
Plausibility/PropLogic/Formula.lean      -- propositional syntax
Plausibility/PropLogic/Semantics.lean    -- models, logical probability
Plausibility/VanHorn/Requirements.lean   -- syntactic R1–R4 (LogicalPlausibility)
Plausibility/VanHorn/Substitution.lean   -- R2/R3 content, diagram Z_i
Plausibility/VanHorn/Reduction.lean      -- Lemma 6, Corollary 8 (syntactic)
Plausibility/VanHorn/Canonic.lean        -- bigOr/exactlyOne, modelsOn, counts
Plausibility/VanHorn/ProbabilityLaws.lean -- Corollary 15, extendedProbability
Plausibility/VanHorn/Counterexamples.lean -- R4 counterexample, biased coin
Plausibility/VanHorn/Bridge.lean         -- R3/R4 transfer, toSystem, calibration
```

## Review report

See `REVIEW.md` (or `REVIEW.pdf`) for the full review report: verified-theorem
inventory, design decisions, the remaining R3/R4 transfer work, pivot options,
and the error points a reviewer should check hardest.
