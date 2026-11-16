import Mathlib
import LeanRealanalysis.ComplexAnalysis.HW4

/-!
# Homework 5: singularities, Schwarz's lemma, Rouché, residues

Formalizations of Homework 5 (Ahlfors, Ch. 4, §3–5).

Mathlib does not (yet) have Rouché's theorem, the argument principle, residues, or the
Schwarz–Pick lemma, so the problems relying on them are stated precisely and left as `sorry`.
-/

open Complex ComplexConjugate Filter Topology Metric Set Polynomial

noncomputable section

namespace HW5

/-! ## Problem 1: entire + nonessential singularity at `∞` ⟹ polynomial -/

/-- "`f` has a nonessential singularity at `∞`" is `MeromorphicAt (fun w ↦ f w⁻¹) 0`. -/
theorem problem1 (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hm : MeromorphicAt (fun w => f w⁻¹) 0) :
    ∃ p : ℂ[X], ∀ z, f z = p.eval z := by
  obtain ⟨n, hn⟩ := hm
  set g := fun w : ℂ => (w - 0) ^ n • f w⁻¹
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hn.continuousAt 1 one_pos
  set C := ‖g 0‖ + 1
  -- `|f z| ≤ C |z|ⁿ` for `|z| > 1/δ`
  have hfar : ∀ z : ℂ, 1 / δ < ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ n := by
    intro z hz
    have hz0 : 0 < ‖z‖ := (by positivity : (0 : ℝ) < 1 / δ).trans hz
    have hz0' : z ≠ 0 := norm_pos_iff.mp hz0
    have hw : dist z⁻¹ 0 < δ := by
      rw [dist_zero_right, norm_inv, inv_lt_comm₀ hz0 hδ, ← one_div]; exact hz
    have h1 := hδ' hw
    have h2 : ‖g z⁻¹‖ ≤ C := by
      have := norm_sub_norm_le (g z⁻¹) (g 0)
      rw [dist_eq_norm] at h1; simp only [C]; linarith
    simp only [g, sub_zero, inv_inv, smul_eq_mul, norm_mul, norm_pow, norm_inv] at h2
    rw [inv_pow, ← div_eq_inv_mul, div_le_iff₀ (by positivity)] at h2
    linarith
  have hC : 0 ≤ C := by positivity
  obtain ⟨p, -, hp⟩ := HW4.problem8 f hf (n + 1) (max (1 / δ + 1) C) fun z hz => by
    have hz1 : 1 / δ < ‖z‖ := by linarith [le_max_left (1 / δ + 1) C]
    have hzC : C ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    calc ‖f z‖ ≤ C * ‖z‖ ^ n := hfar z hz1
      _ ≤ ‖z‖ * ‖z‖ ^ n := mul_le_mul_of_nonneg_right hzC (by positivity)
      _ = ‖z‖ ^ (n + 1) := by ring
  exact ⟨p, hp⟩

/-! ## Problem 2: `eᶻ`, `sin z`, `cos z` have essential singularities at `∞` -/

section Problem2

theorem eval_deriv (p : ℂ[X]) (z : ℂ) :
    deriv (fun z => p.eval z) z = p.derivative.eval z := Polynomial.deriv p

/-- A polynomial with `p = c • p^{(k)}` (`k ≥ 1`) is zero. -/
theorem poly_eq_zero_of_eq_iterate_derivative (p : ℂ[X]) (k : ℕ) (hk : 1 ≤ k) (c : ℂ)
    (h : p = c • derivative^[k] p) : p = 0 := by
  by_contra hp
  have hc : c ≠ 0 := by rintro rfl; rw [zero_smul] at h; exact hp h
  have hdeg : p.natDegree = (derivative^[k] p).natDegree := by
    conv_lhs => rw [h]
    rw [smul_eq_C_mul, natDegree_C_mul hc]
  have hle := natDegree_iterate_derivative p k
  have hpos : k ≤ p.natDegree := by
    by_contra hlt
    push_neg at hlt
    rw [iterate_derivative_eq_zero hlt, smul_zero] at h
    exact hp h
  omega

theorem not_poly_exp : ¬ ∃ p : ℂ[X], ∀ z, exp z = p.eval z := by
  rintro ⟨p, hp⟩
  have hfun : exp = fun z => p.eval z := funext hp
  have h1 : ∀ z, p.eval z = p.derivative.eval z := fun z => by
    rw [← hp, ← eval_deriv, ← hfun, Complex.deriv_exp]
  have := poly_eq_zero_of_eq_iterate_derivative p 1 le_rfl 1 (by
    simpa using Polynomial.funext h1)
  have h0 := hp 0
  rw [this, eval_zero, exp_zero] at h0
  exact one_ne_zero h0

theorem not_poly_sin : ¬ ∃ p : ℂ[X], ∀ z, sin z = p.eval z := by
  rintro ⟨p, hp⟩
  have hfun : sin = fun z => p.eval z := funext hp
  have h1 : ∀ z, cos z = p.derivative.eval z := fun z => by
    rw [← eval_deriv, ← hfun, Complex.deriv_sin]
  have hfun' : cos = fun z => p.derivative.eval z := funext h1
  have h2 : ∀ z, p.eval z = (-1 : ℂ) • (derivative^[2] p).eval z := fun z => by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
      smul_eq_mul]
    rw [← hp, ← eval_deriv, ← hfun', Complex.deriv_cos']; ring
  have := poly_eq_zero_of_eq_iterate_derivative p 2 (by norm_num) (-1)
    (Polynomial.funext fun z => by rw [h2]; simp)
  have h0 := hp (Real.pi / 2)
  rw [this, eval_zero, ← ofReal_ofNat, ← ofReal_div, ← ofReal_sin, Real.sin_pi_div_two] at h0
  norm_num at h0

theorem not_poly_cos : ¬ ∃ p : ℂ[X], ∀ z, cos z = p.eval z := by
  rintro ⟨p, hp⟩
  have hfun : cos = fun z => p.eval z := funext hp
  have h1 : ∀ z, -sin z = p.derivative.eval z := fun z => by
    rw [← eval_deriv, ← hfun, Complex.deriv_cos']
  have hfun' : (fun z => -sin z) = fun z => p.derivative.eval z := funext h1
  have h2 : ∀ z, p.eval z = (-1 : ℂ) • (derivative^[2] p).eval z := fun z => by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
      smul_eq_mul]
    have hd : deriv (fun x => -sin x) z = -cos z :=
      ((hasDerivAt_sin z).neg : HasDerivAt (fun x => -sin x) (-cos z) z).deriv
    rw [← hp, ← eval_deriv, ← hfun', hd]; ring
  have := poly_eq_zero_of_eq_iterate_derivative p 2 (by norm_num) (-1)
    (Polynomial.funext fun z => by rw [h2]; simp)
  have h0 := hp 0
  rw [this, eval_zero, cos_zero] at h0
  exact one_ne_zero h0

theorem problem2_exp : ¬ MeromorphicAt (fun w => exp w⁻¹) 0 := fun h =>
  not_poly_exp (problem1 exp differentiable_exp h)

theorem problem2_sin : ¬ MeromorphicAt (fun w => sin w⁻¹) 0 := fun h =>
  not_poly_sin (problem1 sin differentiable_sin h)

theorem problem2_cos : ¬ MeromorphicAt (fun w => cos w⁻¹) 0 := fun h =>
  not_poly_cos (problem1 cos differentiable_cos h)

end Problem2

/-! ## Problem 3: meromorphic on the extended plane ⟹ rational -/

theorem problem3 (f : ℂ → ℂ) (hf : MeromorphicOn f univ)
    (hinf : MeromorphicAt (fun w => f w⁻¹) 0) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ ∀ᶠ z in cofinite, f z = P.eval z / Q.eval z := by
  sorry

/-! ## Problem 4: `Re f` bounded below ⟹ removable singularity -/

theorem problem4 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r \ {c})) (M : ℝ)
    (hM : ∀ z ∈ ball c r \ {c}, M ≤ (f z).re) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧ EqOn f g (ball c r \ {c}) := by
  set U := ball c r \ {c}
  -- `h = (f - M)/(f - M + 2)` maps into the closed unit disk
  set h := fun z => (f z - M) / (f z - M + 2)
  have hden : ∀ z ∈ U, f z - M + 2 ≠ 0 := by
    intro z hz h0
    have := congrArg re h0
    simp at this
    linarith [hM z hz]
  have hne1 : ∀ z ∈ U, h z ≠ 1 := by
    intro z hz h1
    rw [div_eq_one_iff_eq (hden z hz)] at h1
    have : (0 : ℂ) = 2 := by linear_combination h1
    norm_num at this
  have hle : ∀ z ∈ U, ‖h z‖ ≤ 1 := by
    intro z hz
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden z hz)),
      ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, sub_re, add_re, sub_im, add_im, ofReal_re, ofReal_im, re_ofNat,
      im_ofNat]
    nlinarith [hM z hz]
  have hd : DifferentiableOn ℂ h U :=
    (hf.sub_const _).div ((hf.sub_const _).add_const _) hden
  set H := Function.update h c (limUnder (𝓝[≠] c) h)
  have hH : DifferentiableOn ℂ H (ball c r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hr) hd
      ⟨1, by rintro _ ⟨z, hz, rfl⟩; exact hle z hz⟩
  have hHU : ∀ z ∈ U, H z = h z := fun z hz =>
    Function.update_of_ne (by simpa using hz.2) _ _
  -- `H c ≠ 1` by the maximum modulus principle
  have hHc : H c ≠ 1 := by
    intro hc1
    have hmax : IsMaxOn (norm ∘ H) (ball c r) c := by
      intro z hz
      simp only [Set.mem_setOf_eq, Function.comp, hc1, norm_one]
      by_cases hzc : z = c
      · rw [hzc, hc1, norm_one]
      · rw [hHU z ⟨hz, hzc⟩]; exact hle z ⟨hz, hzc⟩
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball c r).isPreconnected isOpen_ball hH (mem_ball_self hr) hmax
    set z := c + (r / 2 : ℝ)
    have hz : z ∈ U := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]; simp [z, abs_of_pos hr]; linarith
      · simp [z, hr.ne']
    have := hconst hz.1
    simp only [Function.const_apply, hc1, hHU z hz] at this
    exact hne1 z hz this
  have hne1' : ∀ z ∈ ball c r, 1 - H z ≠ 0 := by
    intro z hz h0
    by_cases hzc : z = c
    · rw [hzc] at h0; exact hHc (by linear_combination -h0)
    · rw [hHU z ⟨hz, hzc⟩] at h0; exact hne1 z ⟨hz, hzc⟩ (by linear_combination -h0)
  refine ⟨fun z => M + 2 * H z / (1 - H z), ?_, ?_⟩
  · exact (differentiableOn_const _).add
      ((hH.const_mul 2).div ((differentiableOn_const 1).sub hH) hne1')
  · intro z hz
    simp only
    rw [hHU z hz]
    have h1 := hden z hz
    simp only [h]
    field_simp
    ring

/-! ## Problems 5–8: Schwarz–Pick and its consequences -/

section Problems5to8

/-- **Problem 5** (Schwarz–Pick): `|f(z)| ≤ 1` on the unit disk implies
`|f'(z)| / (1 - |f(z)|²) ≤ 1 / (1 - |z|²)`. -/
theorem problem5 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : MapsTo f (ball 0 1) (closedBall 0 1)) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2) := by
  sorry

/-- **Problem 6**: the half-plane version. -/
theorem problem6 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {z | 0 < z.im})
    (hb : ∀ z, 0 < z.im → 0 ≤ (f z).im) (z z₀ : ℂ) (hz : 0 < z.im) (hz₀ : 0 < z₀.im) :
    ‖(f z - f z₀) / (f z - conj (f z₀))‖ ≤ ‖(z - z₀) / (z - conj z₀)‖ ∧
      ‖deriv f z‖ / (f z).im ≤ 1 / z.im := by
  sorry

/-- **Problem 7**: equality in Schwarz–Pick at one point forces a linear transformation. -/
theorem problem7 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : MapsTo f (ball 0 1) (ball 0 1)) (z₀ : ℂ) (hz₀ : z₀ ∈ ball (0 : ℂ) 1)
    (heq : ‖deriv f z₀‖ / (1 - ‖f z₀‖ ^ 2) = 1 / (1 - ‖z₀‖ ^ 2)) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = (a * z + b) / (c * z + d) := by
  sorry

/-- **Problem 8**: a one-to-one conformal map of the disk onto itself is linear fractional. -/
theorem problem8 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbij : BijOn f (ball 0 1) (ball 0 1)) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = (a * z + b) / (c * z + d) := by
  sorry

end Problems5to8

/-! ## Problems 9–10: counting zeros with Rouché's theorem -/

/-- **Problem 9**: `z⁷ - 2z⁵ + 6z³ - z + 1` has `3` roots (with multiplicity) in `|z| < 1`. -/
theorem problem9 :
    ((X ^ 7 - 2 * X ^ 5 + 6 * X ^ 3 - X + 1 : ℂ[X]).roots.filter (fun z => ‖z‖ < 1)).card = 3 := by
  sorry

/-- **Problem 10**: `z⁴ - 6z + 3` has `3` roots with `1 < |z| < 2`. -/
theorem problem10 :
    ((X ^ 4 - 6 * X + 3 : ℂ[X]).roots.filter (fun z => 1 < ‖z‖ ∧ ‖z‖ < 2)).card = 3 := by
  sorry

/-! ## Problem 11: poles and residues -/

section Problem11

/-- (a) `1/(z² + 5z + 6)`: simple poles at `-2, -3` with residues `1, -1`. -/
theorem problem11_a (z : ℂ) (h2 : z + 2 ≠ 0) (h3 : z + 3 ≠ 0) :
    1 / (z ^ 2 + 5 * z + 6) = 1 / (z + 2) - 1 / (z + 3) := by
  rw [show z ^ 2 + 5 * z + 6 = (z + 2) * (z + 3) by ring]
  field_simp
  ring

/-- (b) `1/(z² - 1)²`: double poles at `±1`, residues `-1/4` at `1` and `1/4` at `-1`. -/
theorem problem11_b (z : ℂ) (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) :
    1 / (z ^ 2 - 1) ^ 2 =
      (1 / 4) / (z - 1) ^ 2 + (-1 / 4) / (z - 1) + (1 / 4) / (z + 1) ^ 2 + (1 / 4) / (z + 1) := by
  rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]
  field_simp
  ring

theorem cos_int_mul_pi' (n : ℤ) : Complex.cos (n * Real.pi) = (-1) ^ n := by
  rw [show ((n : ℂ) * Real.pi) = ((n * Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_int_mul_pi]
  push_cast; ring

/-- (c) `1/sin z`: simple poles at `nπ` with residue `(-1)ⁿ`. -/
theorem problem11_c (n : ℤ) :
    Tendsto (fun z => (z - n * Real.pi) / sin z) (𝓝[≠] (n * Real.pi : ℂ)) (𝓝 ((-1) ^ n)) := by
  have hd : HasDerivAt sin (cos (n * Real.pi)) (n * Real.pi : ℂ) := hasDerivAt_sin _
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  rw [cos_int_mul_pi'] at hs
  have hinv := hs.inv₀ (zpow_ne_zero n (by norm_num))
  rw [show ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n by rw [← inv_zpow, inv_neg, inv_one]] at hinv
  refine hinv.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  rw [slope_def_field, Complex.sin_int_mul_pi, sub_zero, inv_div]

/-- (d) `cot z`: simple poles at `nπ` with residue `1`. -/
theorem problem11_d (n : ℤ) :
    Tendsto (fun z => (z - n * Real.pi) * cot z) (𝓝[≠] (n * Real.pi : ℂ)) (𝓝 1) := by
  have hc : Tendsto cos (𝓝[≠] (n * Real.pi : ℂ)) (𝓝 ((-1) ^ n)) := by
    rw [← cos_int_mul_pi']; exact continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have := (problem11_c n).mul hc
  rw [show ((-1 : ℂ) ^ n * (-1) ^ n) = 1 by rw [← mul_zpow]; norm_num] at this
  refine this.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
  beta_reduce; rw [Complex.cot_eq_cos_div_sin]; ring

/-- (e) `1/sin² z`: double poles at `nπ` with residue `0`; precisely,
`1/sin² z - 1/(z - nπ)²` stays bounded (it tends to `1/3`). -/
theorem problem11_e (n : ℤ) :
    Tendsto (fun z => 1 / sin z ^ 2 - 1 / (z - n * Real.pi) ^ 2) (𝓝[≠] (n * Real.pi : ℂ))
      (𝓝 (1 / 3)) := by
  sorry

/-- (f) `1/(zᵐ(1 - z)ⁿ)`: `Res_{z=0} = C(m+n-2, m-1)` and `Res_{z=1} = -C(m+n-2, m-1)`,
expressed through Cauchy integrals over small circles. -/
theorem problem11_f (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(0, 1 / 2), 1 / (z ^ m * (1 - z) ^ n)) =
        ((m + n - 2).choose (m - 1) : ℂ) ∧
    (2 * Real.pi * I)⁻¹ * (∮ z in C(1, 1 / 2), 1 / (z ^ m * (1 - z) ^ n)) =
        -((m + n - 2).choose (m - 1) : ℂ) := by
  sorry

end Problem11

/-! ## Problem 12: definite integrals by residues -/

section Problem12

open MeasureTheory intervalIntegral

theorem problem12_a (a : ℝ) (ha : 1 < |a|) :
    ∫ x in (0 : ℝ)..Real.pi / 2, 1 / (a + Real.sin x ^ 2) =
      (if 0 < a then 1 else -1) * Real.pi / (2 * Real.sqrt (a * (a + 1))) := by
  sorry

theorem problem12_b :
    ∫ x in Ioi (0 : ℝ), x ^ 2 / (x ^ 4 + 5 * x ^ 2 + 6) =
      Real.pi / 2 * (Real.sqrt 3 - Real.sqrt 2) := by
  sorry

theorem problem12_c :
    ∫ x : ℝ, (x ^ 2 - x + 2) / (x ^ 4 + 10 * x ^ 2 + 9) = 5 * Real.pi / 12 := by
  sorry

theorem problem12_d (a : ℝ) (ha : a ≠ 0) :
    ∫ x in Ioi (0 : ℝ), x ^ 2 / (x ^ 2 + a ^ 2) ^ 3 = Real.pi / (16 * |a| ^ 3) := by
  sorry

theorem problem12_e (a : ℝ) (ha : a ≠ 0) :
    ∫ x in Ioi (0 : ℝ), Real.cos x / (x ^ 2 + a ^ 2) = Real.pi * Real.exp (-|a|) / (2 * |a|) := by
  sorry

/-- (f) is only conditionally convergent, so it is stated as an improper integral. -/
theorem problem12_f (a : ℝ) :
    Tendsto (fun R => ∫ x in (0 : ℝ)..R, x * Real.sin x / (x ^ 2 + a ^ 2)) atTop
      (𝓝 (Real.pi * Real.exp (-|a|) / 2)) := by
  sorry

theorem problem12_g :
    ∫ x in Ioi (0 : ℝ), x ^ (1 / 3 : ℝ) / (1 + x ^ 2) = Real.pi / Real.sqrt 3 := by
  sorry

theorem problem12_h :
    ∫ x in Ioi (0 : ℝ), Real.log x / (1 + x ^ 2) = 0 := by
  sorry

theorem problem12_i (α : ℝ) (h0 : 0 < α) (h2 : α < 2) :
    ∫ x in Ioi (0 : ℝ), Real.log (1 + x ^ 2) / x ^ (1 + α) =
      Real.pi / (α * Real.sin (Real.pi * α / 2)) := by
  sorry

end Problem12

end HW5
