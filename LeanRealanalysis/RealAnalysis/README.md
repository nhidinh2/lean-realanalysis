# Real Analysis: MATH 444 homework

`Math444.lean` contains the MATH 444 exercises, one `section` per problem, each labelled with
its textbook section (§1.2, §2.1, …). It was moved here from the repository root
(`math444_hw.lean`).

## Status

Problems 1–4, 6–9, 14–16 and 20–25 are proved. Problem 5 is proved for sums and differences,
and Problem 19(a) is proved. Problem 26 is only a heading for now.

## Why some problems are left as `sorry`

None of these is blocked by missing Mathlib theory; **they just haven't been finished yet.**
Mathlib has the tools each one needs, such as `limsup`, subsequences and the completeness of
`ℝ`.

| Problem | Statement | What's missing |
|---------|-----------|----------------|
| P5 (`problem5_inv`) | `ℚ(√2)` is closed under reciprocals | rationalising `1/(s + t√2)` and using `√2 ∉ ℚ` to show the denominator `s² − 2t²` is nonzero |
| P10 | two divergent sequences whose sum and product converge | showing `(−1)ⁿ` diverges |
| P11 | an infinite bounded set has an increasing sequence → `sup A` | the recursive construction of the sequence |
| P12 | a bounded sequence has a subsequence → `limsup` | extracting the subsequence |
| P13 | the "every subsequence has a sub-subsequence → 0" step | building the bad subsequence by dependent choice; the rest of the proof is done |
| P17 | `limsup (x + y) ≤ limsup x + limsup y` | the boundedness side conditions for Mathlib's `limsup` lemmas |
| P18 | Cauchy condensation test | the two comparison estimates |
| P19(b) | `f(x) = x·1_ℚ(x)` has no limit at `c ≠ 0` | density of ℚ and of ℝ∖ℚ near `c` |

## Cleanup notes

- Problem 25 used to live in a separate file whose proof no longer compiled (`CauchySeq.mul` is
  the *group* lemma). Its proof is now in `Math444.lean`: Cauchy ⇒ convergent in `ℝ`, then use
  the product of limits. Your paper proof is kept there as a comment.
- Four errors caused by Mathlib changes were fixed. P7 now uses `Real.sInf_def`. P19 needed
  `open Classical` for the `if`. P19(a) needed one small tactic fix. P20 had an argument-passing
  change.
