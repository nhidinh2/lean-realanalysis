# Complex Analysis: Homeworks 1–6

Lean formalizations of complex-analysis Homeworks 1–6, which follow Ahlfors's *Complex Analysis*.
Each file has one `section` per problem, and each problem is a theorem named `problemN…` whose
conclusion is the boxed answer from the written solutions.

| File | Topic | Proved | `sorry` |
|------|-------|--------|---------|
| `HW1.lean` | Complex numbers: roots, \|(a−b)/(1−āb)\|, Lagrange's identity, de Moivre | 11 / 11 | 0 |
| `HW2.lean` | Harmonic functions, partial fractions, power series, exp and log | all but 1 | 1 |
| `HW3.lean` | Linear (Möbius) transformations, cross ratios, reflections | all but 1 | 1 |
| `HW4.lean` | Contour integrals, Cauchy's formula, Cauchy's estimates | all but parts of P7 | 4 |
| `HW5.lean` | Singularities, Schwarz's lemma, Rouché's theorem, residues | P1, P2, P4, P11(a–d) | 18 |
| `HW6.lean` | Uniform convergence, ζ, Taylor and Laurent series, Bernoulli numbers | P1, P2, P4, P7 (core), P8 | 4 |

Every file compiles. A `sorry` means the statement is written out exactly but the proof is
missing.

## Why some problems are left as `sorry`

The main reason is that **Mathlib does not yet have the theory these solutions use.** In
particular it has no:

- **residues or the residue theorem**,
- **argument principle or Rouché's theorem**,
- **Schwarz–Pick lemma** (it has the Schwarz lemma only for maps between disks centred at
  `f(c)`),
- **Cauchy integral formula for derivatives at a point other than the circle's centre**.

Proving these problems would mean building that theory first, which is a project in its own
right. A few others are just long computations that haven't been done yet.

### HW2
- **P11 (second part), radius of `∑ aₙ² zⁿ` is `R²`**: this needs the Cauchy–Hadamard formula
  `1/R = limsup |aₙ|^{1/n}` in a form that can be squared, and Mathlib doesn't expose
  `FormalMultilinearSeries.radius` that way. The first part, the radius of `∑ aₙ z²ⁿ`, is
  proved.

### HW3
- **P11, concentric circles keep their radius ratio**: the written proof uses the *symmetry
  principle*, which Mathlib doesn't have. A purely algebraic proof exists, comparing
  coefficients of `|az+b|² = ρ²|cz+d|²` on each circle, but it is long and hasn't been
  written yet.

### HW4
- **P7(ii), three cases with negative exponents**: the pole sits at `z = 1` inside `|z| = 2`
  but is not the circle's centre. Mathlib's formula for higher derivatives only works at the
  centre, and moving the contour would need a homotopy or residue theorem.
- **P7(iii), `∫ |z−a|⁻⁴ |dz|`**: the written solution evaluates it by residues.

### HW5
- **P3, meromorphic on the Riemann sphere ⇒ rational**: needs "finitely many poles by
  compactness" plus pole-order bookkeeping that Mathlib's meromorphic API doesn't package.
- **P5–P8, Schwarz–Pick and its consequences**: Schwarz–Pick is not in Mathlib. P6–P8 also need
  Möbius automorphisms of the disk and the half-plane, and their equality cases.
- **P9, P10, counting roots**: these use **Rouché's theorem**, which Mathlib doesn't have.
- **P11(e), (f), residues of `1/sin²z` and `1/(zᵐ(1−z)ⁿ)`**: Mathlib has no residue, so these
  are stated as limits and as Cauchy integrals. Proving them needs Laurent-series manipulation.
  P11(a)–(d) are proved.
- **P12(a)–(i), definite integrals by residues**: each needs the residue theorem plus estimates
  on large semicircles and keyhole contours. Some, like (b) and (c), could be done instead with
  real partial fractions and `arctan`; that's possible future work. (f) is stated as an
  improper integral because it doesn't converge absolutely.

### HW6
- **P3, generalisation of Hurwitz's theorem**: uses Rouché's theorem or the argument principle.
- **P5, `log(sin z / z)` up to `z⁶`**: needs composition of power series with `O(z⁸)` control.
  Mathlib's support for this is too low-level to make it practical.
- **P6, the `z⁷` coefficient of `tan z` is `17/315`**: the linear system the solution solves is
  checked (`problem6_system`). Linking it to `iteratedDeriv 7 tan 0` needs Taylor coefficients
  of a quotient.
- **P7, full Schwarzian statement**: the leading-term algebra is proved
  (`problem7_leading`). The `O((z−z₀)⁻¹)` statement for a general meromorphic `f` needs
  Laurent expansions of `f′, f″, f‴`.

## Changes from the written statements

- Lean defines `x / 0 = 0`, so hypotheses such as `z ≠ -1` are added where the paper assumes an
  expression is defined.
- "Radius of convergence `R`" is stated as "converges for `|z| < R` and diverges for
  `|z| > R`".
- Contour integrals over circles use Mathlib's `∮ z in C(c, R), f z`.
- Residues are expressed as limits, partial-fraction identities or Cauchy integrals, because
  Mathlib has no residue function.
