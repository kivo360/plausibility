# READING.md — How to read this repo without knowing Mathlib

Written for a reviewer who knows logic but is new to Lean/Mathlib. It answers
the questions that cost me the most time when I started.

## The question everyone hits first: "where is `Finset.univ.filter` defined?"

It isn't — there's no such definition. Lean's dot notation is just
namespace-qualified application:

```
Finset.univ.filter (fun v => φ.eval v = true)
        ↕
Finset.filter (fun v => φ.eval v = true) Finset.univ
```

Two independent pieces:

| Piece | Defined in (vendored inside this repo) |
|---|---|
| `Finset.filter` | `.lake/packages/mathlib/Mathlib/Data/Finset/Filter.lean:52` — `def filter (s : Finset α) : Finset α := ⟨_, s.2.filter p⟩` (keeps elements of `s` satisfying predicate `p`) |
| `Finset.univ` | `.lake/packages/mathlib/Mathlib/Data/Fintype/Defs.lean:92` — the "all elements" Finset, built from a `Fintype α` instance (finite-type enumeration) |

You'll meet them together on day one because this repo's `models φ`
(`Plausibility/PropLogic/Semantics.lean:22`) is literally
"all valuations, filtered to those satisfying φ" — the finite model set.

## Three ways to find where ANY Mathlib thing lives

1. **It's already on your disk.** The full Mathlib source is vendored at
   `.lake/packages/mathlib/Mathlib/`. Grep it like normal code:
   ```bash
   grep -rn "def filter" .lake/packages/mathlib/Mathlib/Data/Finset/
   ```
2. **The searchable docs** (every entry links to exact source line):
   https://leanprover-community.github.io/mathlib4_docs/
3. **Ask the compiler** — make a scratch file and run it through Lean:
   ```bash
   cat > /tmp/q.lean << 'EOF'
   import Mathlib
   #check @Finset.filter        -- full signature
   example : True := by
     trace_state                -- goal display
     trivial
   EOF
   lake env lean /tmp/q.lean
   ```
   In VS Code with the Lean extension, F12 / cmd-click on any identifier jumps
   to its definition (into the vendored Mathlib) — usually the fastest way.

## Idiom cheat-sheet (everything that recurs in this repo)

| You see | It means |
|---|---|
| `Finset α` | finite set of `α`s, with no duplicates — our "finite world space" |
| `↥S` (or `{w // w ∈ S}`) | the *subtype*: elements of `S` carrying proof of membership. A type, so you can quantify over it |
| `w ∈ modelsOn S φ` | membership; the workhorse bridge lemma `mem_modelsOn_iff` turns it into `φ.eval (fillTrue S w) = true` |
| `Fintype.card X` vs `X.card` | "size of type `X`" vs "size of Finset `X`". Equal for `↥S` via `Fintype.card_coe` |
| `.attach` | turns `s : Finset α` into `Finset ↥s` (elements + proofs) — appears in the final theorem's event |
| `[DecidableEq α]`, `[DecidablePred p]` | "computability plumbing": finite sets need decidable equality/membership to build `filter` etc. Ignore on first read |
| `decide` / `native_decide` | turn a decidable proposition into a proof. `native_decide` trusts the compiled evaluator (used only in sanity checks) |
| `∑ x ∈ s, f x` | finite sum (`Finset.sum`) — used in counting arguments |
| `omega` | automated arithmetic (linear ℕ/ℤ) |
| `simp only [lem]` | rewrite with exactly the lemmas listed; `simp` = "rewrite with everything marked safe" |
| `calc a = b := proof` | chained equalities — the native style of this repo |
| `set x := e with h` / `let x := e` | introduce an abbreviation. (`set` makes it opaque to `omega`/`rw` — a real footgun, see REVIEW §5) |
| structure `PlausibilitySystem P` with fields | a record whose fields are the axioms R1–R4's semantic analogues — assumptions, given per-instance, never global axioms |
| `noncomputable def` | definition needing classical choice (can't run, only reason about) |
| `#print axioms thm` | prints what `thm` ultimately depends on. Ours: `[propext, Classical.choice, Quot.sound]` — the standard three, nothing else |

## Suggested reading order (dependency order, easiest first)

**Semantic layer** (self-contained, ~1 afternoon):
1. `Plausibility/Basic.lean` — `EventEquiv`, the `PlausibilitySystem` structure (the three laws)
2. `Plausibility/Canonical.lean` — every event = canonical m-of-n (Lemma 6/Cor 8)
3. `Plausibility/ScaleInvariant.lean` — (m,n) ~ (km,kn) (Lemma 10)
4. `Plausibility/RationalRepresentation.lean` — only the ratio matters; strict monotone (Lemma 13)
5. `Plausibility/ProbabilityTheorem.lean` — the order-isomorphism with ℚ∩[0,1] (Theorem 14) + consistency (Thm 16)

**Propositional layer**:
6. `Plausibility/PropLogic/Formula.lean` → `Semantics.lean` — syntax, `models`, `logicalProbability`
7. `Plausibility/VanHorn/Requirements.lean` — the raw syntactic R1–R4 (`LogicalPlausibility`)
8. `Plausibility/VanHorn/Substitution.lean` — what R2/R3 *mean* semantically
9. `Plausibility/VanHorn/Canonic.lean` — `bigOr`/`exactlyOne`, `modelsOn`, counting lemmas
10. `Plausibility/VanHorn/Reduction.lean` — Lemma 6 from raw R1+R2 (the four-step grind)
11. `Plausibility/VanHorn/Bridge.lean` — R3/R4 transfer, `toSystem`, final `vanHorn_calibration`
12. `Plausibility/VanHorn/Counterexamples.lean` — R4 is not derivable from R1–R3

**The statements matter more than the proofs.** Read each `theorem` line and its
docstring first; the proof bodies are long but the claims are one-liners. The
load-bearing statements: `value_eq_of_counts_eq` (Reduction), `toSystem`
(Bridge), `vanHorn_calibration` (Bridge), `plausibilityOrderIso`
(ProbabilityTheorem).

## Building and poking

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build                                       # full check (green)
lake env lean Plausibility/VanHorn/Bridge.lean  # type-check one file
```

Add `#check foo` anywhere temporarily; `lake env lean <file>` prints it.
Don't run `lake update` — everything is pinned to v4.33.1.
