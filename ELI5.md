# The Dumb-Simple Version

(No math background needed. If a sentence feels complicated, I've failed — skip to the summary at the bottom.)

## What question does this answer?

A guy named Van Horn asked: **"If I want to measure how plausible a belief is, and I'm not an idiot about it, what am I forced to get?"**

His answer: **probability.** The thing with fractions between 0 and 1. There is no clever alternative.

That sounds like an opinion. It's not — it's a theorem. And now a computer has checked every single step of it.

## The four "don't be an idiot" rules

Imagine you score beliefs with some made-up plausibility meter. Van Horn says: if your meter obeys these four obvious rules, your meter *is* probability. No escape.

1. **Saying the same thing differently doesn't change anything.**
   "It rains AND it's Tuesday" vs "It's Tuesday AND it rains" — same plausibility. Renaming stuff, adding filler words: doesn't matter.

2. **Defining a new word doesn't change anything.**
   Call a rainy Tuesday a "blorptday". Now "it's a blorptday" is just shorthand. Your plausibility of rain-on-Tuesday can't change because you invented a nickname for it.

3. **Irrelevant stuff doesn't change anything.**
   Flip a coin you never look at, in a room you never enter. Your belief about the weather can't move because of that coin.

4. **More evidence, more belief. Strictly.**
   If "A" gives you *strictly more cases* than "B" out of the same total, then A must be *strictly* more plausible than B. No ties, no weird flat spots.

That's it. Four rules of not-being-dumb.

## The punchline

Follow the four rules and your plausibility for "A, given X" is *forced* to be:

```
number of cases where A and X both hold
─────────────────────────────────────────
number of cases where X holds
```

Exactly the probability formula you learned in school. The rules leave zero room for anything else. Your clever alternative scoring system? Either it's probability in disguise, or it breaks at least one rule.

Bonus: the achievable scores line up perfectly in order with the rationals in [0,1]. Not just "some function of probability" — probability itself, in order.

## What did we actually do?

We made a computer program (Lean, a proof assistant) verify Van Horn's entire argument, line by line. Every "obviously" and "it follows that" in the paper is now a checked step.

Why bother? Humans make mistakes in long proofs. The computer doesn't accept hand-waving. If it says `Build completed successfully`, the theorem is true — not probably true, *true* — assuming only the three standard built-in axioms of the proof system. We checked: every theorem in the repo lists exactly `[propext, Classical.choice, Quot.sound]` and nothing else. No `sorry` (that's the escape hatch that means "trust me" — we have zero).

## The honest small print

- We verified the **finite** version: finitely many situations, finitely many atoms. The paper's extension to infinite domains (measure theory) is real math but out of scope here.
- If your premise X is impossible (zero cases), the formula divides by zero. The paper excludes that case; so do we.
- One rule is genuinely necessary: we built a concrete counterexample (`threeSystem` in `Counterexamples.lean`) that obeys rules 1–3 but breaks rule 4 and is NOT probability. So you can't drop rule 4 and keep the theorem. Nice to know it's not decorative.
- We also built a "does the machine even work" check: the plain counting measure satisfies all four rules (Theorem 16), so the theorem isn't vacuously true — real examples exist.

## One-paragraph summary for your last brain cell

**Common sense about belief, written as four rules, mathematically forces your beliefs to be probabilities. We made a computer check the whole argument. It's done, it's green, it's on GitHub.**

## Repo map for later

| If you want... | Look at |
|---|---|
| The final "it's probability" theorem | `Plausibility/VanHorn/Bridge.lean` → `vanHorn_calibration` |
| The semantic core (order ≅ rationals in [0,1]) | `Plausibility/ProbabilityTheorem.lean` |
| Rules 1+2 grinding everything down to counting | `Plausibility/VanHorn/Reduction.lean` |
| Rule 3 (irrelevant coin flips) doing the scaling | `Plausibility/VanHorn/Bridge.lean` → `value_scale` |
| Rule 4 (strictness) doing the ordering | `Plausibility/VanHorn/Bridge.lean` → `value_mono_canonical` |
| The counterexample showing rule 4 is needed | `Plausibility/VanHorn/Counterexamples.lean` |
| The full technical review report | `REVIEW.md` / `REVIEW.pdf` |
