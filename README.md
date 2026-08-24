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

## What is proved

The project is layered exactly as the paper's argument runs:

```
Propositional problem (A | X)                 [PropLogic/ — syntax only]
          ↓  (paper's R1 + R2, Lemma 6 — NOT yet formalized syntactically)
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

### Propositional layer

* `PropLogic/Formula.lean` — syntax (`atom`, `bot`, `neg`, `and`, derived
  `or`/`imp`/`iff`/`top`) and Boolean evaluation.
* `PropLogic/Semantics.lean` — `models φ` as a `Finset (α → Bool)`,
  `Satisfiable`, `logicalProbability A X = #(A ∧ X) / #X` with
  `0 ≤ · ≤ 1`, plus four `native_decide` exhaustive-enumeration sanity checks.
* `eventOf` / `score_eventOf` — the bridge (milestone 9): for a satisfiable
  premise `X`, scoring the event of `X`-worlds satisfying `A` equals the
  plausibility of the logical probability `#models(A ∧ X) / #models X`.
* `Sanity` section — `(1,2) = (2,4)` in plausibility (Lemma 10) and
  `(1,3) < (1,2)` (Lemma 13), for *every* plausibility system.

## Honest scope statement

This covers the paper's **finite uniqueness theorem** at the semantic layer:
the formalization starts from the semantic consequence of R1 + R2
(invariance under change of variables, which the paper derives from the
syntactic R1 + R2 via fresh-symbol definitions — Lemma 6's renaming and
substitution machinery is not formalized here). The measure-theoretic
extension to infinite domains (paper §9.3) is out of scope. Unsatisfiable
premises are excluded from the main theorems, as in the paper.

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
```

## Review report

See `REVIEW.md` (or `REVIEW.pdf`) for the full review report: verified-theorem
inventory, design decisions, the remaining Lemma-6 bridge work, pivot options,
and the error points a reviewer should check hardest.
