import Mathlib

/-!
# Homework 4: complex integration, Cauchy's formula and estimates

Formalizations of Homework 4 (Ahlfors, Ch. 4). Contour integrals over circles use Mathlib's
`circleIntegral`, written `∮ z in C(c, R), f z`.
-/

open Complex ComplexConjugate Filter Topology Metric Set
open scoped Nat

noncomputable section

namespace HW4

/-! ### Helpers -/

theorem ci_inv {c w : ℂ} {R : ℝ} (hw : w ∉ sphere c |R|) :
    CircleIntegrable (fun z => (z - w)⁻¹) c R :=
  circleIntegrable_sub_inv_iff.mpr (Or.inr hw)

theorem ci_const_mul {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (a : ℂ) (hf : CircleIntegrable f c R) :
    CircleIntegrable (fun z => a * f z) c R :=
  (show IntervalIntegrable _ _ _ _ from hf).const_mul a

theorem not_mem_sphere_of_norm_lt {w : ℂ} {R : ℝ} (hw : ‖w‖ < R) : w ∉ sphere (0 : ℂ) |R| := by
  intro h
  rw [mem_sphere, dist_zero_right, abs_of_pos ((norm_nonneg w).trans_lt hw)] at h
  linarith

/-! ## Problem 1: `∮_{|z|=r} x dz = π i r²` -/

theorem problem1 (r : ℝ) (hr : 0 < r) : (∮ z in C(0, r), (z.re : ℂ)) = Real.pi * I * r ^ 2 := by
  have hcongr : EqOn (fun z : ℂ => (z.re : ℂ))
      (fun z => (1 / 2 : ℂ) * z + ((r : ℂ) ^ 2 / 2) * (z - 0)⁻¹) (sphere 0 r) := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    have hconj : conj z = (r : ℂ) ^ 2 / z := by
      rw [eq_div_iff hz0, mul_comm, mul_conj, normSq_eq_norm_sq, hz]; push_cast; ring
    simp only
    rw [re_eq_add_conj, hconj, sub_zero]
    field_simp
  have hint1 : CircleIntegrable (fun z : ℂ => (1 / 2 : ℂ) * z) 0 r :=
    (continuous_const.mul continuous_id).continuousOn.circleIntegrable'
  have hint2 : CircleIntegrable (fun z : ℂ => ((r : ℂ) ^ 2 / 2) * (z - 0)⁻¹) 0 r :=
    ci_const_mul _ (ci_inv (not_mem_sphere_of_norm_lt (by simpa using hr)))
  have hz : (∮ z in C(0, r), z) = 0 := by
    simpa using circleIntegral.integral_sub_zpow_of_ne (by decide : (1 : ℤ) ≠ -1) 0 0 r
  rw [circleIntegral.integral_congr hr.le hcongr, circleIntegral.integral_add hint1 hint2,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul, hz,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]
  ring

/-! ## Problem 2: `∮_{|z|=2} dz/(z² - 1) = 0` -/

theorem problem2 : (∮ z in C(0, 2), 1 / (z ^ 2 - 1)) = 0 := by
  have hcongr : EqOn (fun z : ℂ => 1 / (z ^ 2 - 1))
      (fun z => (1 / 2 : ℂ) * ((z - 1)⁻¹ - (z - -1)⁻¹)) (sphere 0 2) := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    have h1 : z - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hz; norm_num at hz
    have h2 : z - -1 ≠ 0 := by
      intro h; rw [show z = -1 by linear_combination h] at hz; norm_num at hz
    have h3 : z ^ 2 - 1 ≠ 0 := by
      rw [show z ^ 2 - 1 = (z - 1) * (z - -1) by ring]; exact mul_ne_zero h1 h2
    simp only
    field_simp
    ring
  have hin : ∀ w : ℂ, ‖w‖ < 2 → (∮ z in C(0, 2), (z - w)⁻¹) = 2 * Real.pi * I := fun w hw =>
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hw)
  rw [circleIntegral.integral_congr (by norm_num) hcongr, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (ci_inv (not_mem_sphere_of_norm_lt (by norm_num)))
      (ci_inv (not_mem_sphere_of_norm_lt (by norm_num))),
    hin 1 (by norm_num), hin (-1) (by norm_num)]
  ring

/-! ## Problem 3: `∮ conj(f) f' dz` is purely imaginary -/

/-- For `f` analytic near the circle (with `f'` continuous there), `∮ f̄ f' dz` is purely
imaginary, since its real part is `½ ∮ d|f|²` over a closed curve. -/
theorem problem3 (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, DifferentiableAt ℂ f z) (hf' : ContinuousOn (deriv f) (sphere c R)) :
    (∮ z in C(c, R), conj (f z) * deriv f z).re = 0 := by
  have hγ : ∀ θ, circleMap c R θ ∈ sphere c R := fun θ => circleMap_mem_sphere c hR θ
  set g : ℝ → ℂ := fun θ => f (circleMap c R θ)
  set g' : ℝ → ℂ := fun θ => deriv f (circleMap c R θ) * (circleMap 0 R θ * I)
  have hg : ∀ θ, HasDerivAt g (g' θ) θ := fun θ =>
    (hf _ (hγ θ)).hasDerivAt.comp θ (hasDerivAt_circleMap c R θ)
  have hcg : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  have hcg' : Continuous g' :=
    (hf'.comp_continuous (continuous_circleMap c R) hγ).mul
      ((continuous_circleMap 0 R).mul continuous_const)
  -- `N = g ḡ = |g|²` has derivative `g' ḡ + g ḡ'`, and `N(2π) = N(0)`
  set N' : ℝ → ℂ := fun θ => g' θ * star (g θ) + g θ * star (g' θ)
  have hN : ∀ θ, HasDerivAt (fun θ => g θ * star (g θ)) (N' θ) θ := fun θ =>
    (hg θ).mul (hg θ).star
  have hcN' : Continuous N' := by
    simp only [N']; exact (hcg'.mul hcg.star).add (hcg.mul hcg'.star)
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, N' θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hN θ)
      (hcN'.intervalIntegrable _ _)]
    have hp : circleMap c R (2 * Real.pi) = circleMap c R 0 := by
      simpa using periodic_circleMap c R 0
    simp only [g, hp, sub_self]
  -- rewrite the circle integral
  have hI : (∮ z in C(c, R), conj (f z) * deriv f z) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, star (g θ) * g' θ := by
    unfold circleIntegral
    congr 1; funext θ
    simp only [g, g', deriv_circleMap, smul_eq_mul, Complex.star_def]
    ring
  have hcJ : Continuous fun θ => star (g θ) * g' θ := hcg.star.mul hcg'
  have hpt : ∀ θ, (star (g θ) * g' θ).re = (1 / 2) * (N' θ).re := fun θ => by
    simp only [N', Complex.star_def, mul_re, add_re, conj_re, conj_im]; ring
  rw [hI, ← reCLM_apply, ← (reCLM).intervalIntegral_comp_comm (hcJ.intervalIntegrable _ _)]
  simp only [reCLM_apply, hpt]
  rw [intervalIntegral.integral_const_mul]
  have : (∫ θ in (0 : ℝ)..2 * Real.pi, (N' θ).re) = (∫ θ in (0 : ℝ)..2 * Real.pi, N' θ).re := by
    rw [← reCLM_apply, ← (reCLM).intervalIntegral_comp_comm (hcN'.intervalIntegrable _ _)]
    rfl
  rw [this, hint, zero_re, mul_zero]

/-! ## Problem 4: `∮ f'/f = 0` when `|f - 1| < 1` -/

theorem problem4 (f : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    (h1 : ∀ z ∈ Ω, ‖f z - 1‖ < 1) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hsub : sphere c R ⊆ Ω) :
    (∮ z in C(c, R), deriv f z / f z) = 0 := by
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt' (f := fun z => log (f z))
  intro z hz
  rw [abs_of_nonneg hR] at hz
  have hzΩ := hsub hz
  have hd : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (hΩ.mem_nhds hzΩ)).hasDerivAt
  have hslit : f z ∈ slitPlane := by
    have h := h1 z hzΩ
    have h' := Complex.abs_re_le_norm (f z - 1)
    rw [sub_re, one_re] at h'
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [neg_abs_le ((f z).re - 1)]))
  exact (hd.clog hslit).hasDerivWithinAt

/-! ## Problem 5: `∮_{|z|=1} e^z / z dz = 2πi` -/

theorem problem5 : (∮ z in C(0, 1), exp z / z) = 2 * Real.pi * I := by
  have := (differentiable_exp.diffContOnCl (s := ball (0 : ℂ) 1)).circleIntegral_sub_inv_smul
    (mem_ball_self one_pos)
  simp only [sub_zero, smul_eq_mul, exp_zero, mul_one] at this
  simpa [div_eq_inv_mul] using this

/-! ## Problem 6: `∮_{|z|=2} dz/(z² + 1) = 0` -/

theorem problem6 : (∮ z in C(0, 2), 1 / (z ^ 2 + 1)) = 0 := by
  have hcongr : EqOn (fun z : ℂ => 1 / (z ^ 2 + 1))
      (fun z => (1 / (2 * I)) * ((z - I)⁻¹ - (z - -I)⁻¹)) (sphere 0 2) := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    have h1 : z - I ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hz; norm_num at hz
    have h2 : z - -I ≠ 0 := by
      intro h; rw [show z = -I by linear_combination h] at hz; norm_num at hz
    have h3 : z ^ 2 + 1 ≠ 0 := by
      rw [show z ^ 2 + 1 = (z - I) * (z - -I) by ring_nf; rw [I_sq]; ring]
      exact mul_ne_zero h1 h2
    simp only
    field_simp
    linear_combination (-2 * I) * I_sq
  have hin : ∀ w : ℂ, ‖w‖ < 2 → (∮ z in C(0, 2), (z - w)⁻¹) = 2 * Real.pi * I := fun w hw =>
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hw)
  rw [circleIntegral.integral_congr (by norm_num) hcongr, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (ci_inv (not_mem_sphere_of_norm_lt (by simp)))
      (ci_inv (not_mem_sphere_of_norm_lt (by simp))),
    hin I (by simp), hin (-I) (by simp)]
  ring

/-! ## Problem 7 -/

section Problem7

/-- (i) `∮_{|z|=1} e^z z^{-(n+1)} dz = 2πi / n!`. -/
theorem problem7_1_pos (n : ℕ) :
    (∮ z in C(0, 1), exp z / z ^ (n + 1)) = 2 * Real.pi * I / n ! := by
  have := (differentiable_exp.diffContOnCl (s := ball (0 : ℂ) 1)).circleIntegral_one_div_sub_center_pow_smul
    one_pos n
  rw [iteratedDeriv_eq_iterate, iter_deriv_exp, exp_zero, smul_eq_mul, mul_one] at this
  simpa [div_eq_inv_mul] using this

/-- (i) `∮_{|z|=1} e^z z^m dz = 0` for `m ≥ 0` (entire integrand). -/
theorem problem7_1_nonpos (m : ℕ) : (∮ z in C(0, 1), exp z * z ^ m) = 0 :=
  ((differentiable_exp.mul (differentiable_pow m)).diffContOnCl).circleIntegral_eq_zero zero_le_one

/-- (ii), case `n, m ≥ 0`: the integrand is a polynomial. -/
theorem problem7_2_nonneg (n m : ℕ) : (∮ z in C(0, 2), z ^ n * (1 - z) ^ m) = 0 :=
  (((differentiable_pow n).mul ((differentiable_const 1).sub differentiable_id |>.pow m)
    ).diffContOnCl).circleIntegral_eq_zero zero_le_two

/-- (ii), case `n ≥ 0, m = -k < 0`: `2πi (-1)^k C(n, k-1)`. -/
theorem problem7_2_neg_m (n k : ℕ) (hk : 1 ≤ k) :
    (∮ z in C(0, 2), z ^ n / (1 - z) ^ k) = 2 * Real.pi * I * (-1) ^ k * (n.choose (k - 1)) := by
  sorry

/-- (ii), case `n = -j < 0, m ≥ 0`: `2πi (-1)^(j-1) C(m, j-1)`. -/
theorem problem7_2_neg_n (j m : ℕ) (hj : 1 ≤ j) :
    (∮ z in C(0, 2), (1 - z) ^ m / z ^ j) = 2 * Real.pi * I * (-1) ^ (j - 1) * (m.choose (j - 1)) := by
  sorry

/-- (ii), case `n, m < 0`: the integral vanishes (let the radius go to `∞`). -/
theorem problem7_2_neg_neg (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∮ z in C(0, 2), 1 / (z ^ j * (1 - z) ^ k)) = 0 := by
  sorry

/-- (iii) `∫_{|z|=ρ} |z - a|^{-4} |dz| = 2πρ(ρ² + |a|²)/|ρ² - |a|²|³`. -/
theorem problem7_3 (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ha : ‖a‖ ≠ ρ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, ρ / ‖circleMap 0 ρ θ - a‖ ^ 4 =
      2 * Real.pi * ρ * (ρ ^ 2 + ‖a‖ ^ 2) / |ρ ^ 2 - ‖a‖ ^ 2| ^ 3 := by
  sorry

end Problem7

/-! ## Problem 8: entire functions of polynomial growth are polynomials -/

theorem problem8 (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℕ) (R₀ : ℝ)
    (hbound : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z, f z = p.eval z := by
  -- Step 1: the Taylor coefficients of order `k > n` vanish (Cauchy's estimate, `R → ∞`).
  have hvanish : ∀ k, n < k → iteratedDeriv k f 0 = 0 := by
    intro k hk
    by_contra hne
    set δ := ‖iteratedDeriv k f 0‖
    have hδ : 0 < δ := norm_pos_iff.mpr hne
    set R := max (max R₀ 1) ((k ! : ℝ) / δ + 1)
    have hR1 : 1 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
    have hR0 : 0 < R := by linarith
    have hRR₀ : R₀ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    have hRk : (k ! : ℝ) / δ < R := by
      have := le_max_right (max R₀ 1) ((k ! : ℝ) / δ + 1); linarith
    have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0
      hf.diffContOnCl (C := R ^ n) (c := 0) fun z hz => by
        rw [mem_sphere, dist_zero_right] at hz
        rw [← hz]; exact hbound z (hz ▸ hRR₀)
    -- `k! Rⁿ / Rᵏ ≤ k! / R < δ`
    have hpow : R ^ n * R ≤ R ^ k := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hR1 hk
    have h1 : (k ! : ℝ) * R ^ n / R ^ k ≤ k ! / R := by
      rw [div_le_div_iff₀ (by positivity) hR0]
      have := Nat.cast_nonneg (α := ℝ) k !
      nlinarith
    have h2 : (k ! : ℝ) / R < δ := by
      rw [div_lt_iff₀ hR0]; rw [div_lt_iff₀ hδ] at hRk; linarith
    linarith
  -- Step 2: the Taylor series is a finite sum.
  refine ⟨∑ k ∈ Finset.range (n + 1), Polynomial.C ((k ! : ℂ)⁻¹ * iteratedDeriv k f 0) *
    Polynomial.X ^ k, ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by simp at hk; omega)
  · have hT := Complex.hasSum_taylorSeries_of_entire hf 0 z
    have hfin : HasSum (fun k : ℕ => (k ! : ℂ)⁻¹ • (z - 0) ^ k • iteratedDeriv k f 0)
        (∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ • (z - 0) ^ k • iteratedDeriv k f 0) := by
      apply hasSum_sum_of_ne_finset_zero
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [hvanish k (by omega), smul_zero, smul_zero]
    rw [hT.unique hfin, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_eq_mul, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring

/-! ## Problem 9: Cauchy's estimate inside a disk -/

theorem problem9 (f : ℂ → ℂ) (R M ρ : ℝ) (hf : DiffContOnCl ℂ f (ball 0 R))
    (hM : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ M) (hρR : ρ < R) (z : ℂ) (hz : ‖z‖ ≤ ρ) (n : ℕ) :
    ‖iteratedDeriv n f z‖ ≤ n ! * M / (R - ρ) ^ n := by
  set r := R - ‖z‖
  have hr : 0 < r := by simp only [r]; linarith
  have hball : ball z r ⊆ ball 0 R := by
    intro w hw
    rw [mem_ball] at hw ⊢
    calc dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ < r + ‖z‖ := by rw [dist_zero_right]; linarith
      _ = R := by simp [r]
  have hsph : ∀ w ∈ sphere z r, ‖f w‖ ≤ M := by
    intro w hw
    apply hM
    rw [mem_closedBall]
    calc dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ = r + ‖z‖ := by rw [mem_sphere.mp hw, dist_zero_right]
      _ = R := by simp [r]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp; linarith [norm_nonneg z]))
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr (hf.mono hball) hsph
  refine hest.trans (div_le_div_of_nonneg_left (by positivity) (by
    apply pow_pos; linarith) (pow_le_pow_left₀ (by linarith) (by simp only [r]; linarith) n))

/-! ## Problem 10: `|f(z)| ≤ 1/(1 - |z|)` on the unit disk -/

theorem problem10_r (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1 / (1 - ‖z‖)) (n : ℕ) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) : ‖iteratedDeriv n f 0‖ ≤ n ! / (r ^ n * (1 - r)) := by
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0
    (hf.diffContOnCl_ball hcl) (C := 1 / (1 - r)) fun z hz => by
      have := hb z (hcl (sphere_subset_closedBall hz))
      rw [mem_sphere, dist_zero_right] at hz; rwa [hz] at this
  calc ‖iteratedDeriv n f 0‖ ≤ n ! * (1 / (1 - r)) / r ^ n := hest
    _ = n ! / (r ^ n * (1 - r)) := by field_simp

/-- The best estimate: choosing `r = n/(n+1)` gives `|f^(n)(0)| ≤ n! (n+1)^{n+1} / nⁿ`. -/
theorem problem10 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1 / (1 - ‖z‖)) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedDeriv n f 0‖ ≤ n ! * ((n + 1 : ℝ) ^ (n + 1) / (n : ℝ) ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := problem10_r f hf hb n (n / (n + 1)) (by positivity) (by
    rw [div_lt_one (by positivity)]; linarith)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have e : ((n : ℝ) / (n + 1)) ^ n * (1 - n / (n + 1)) = (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) := by
    rw [div_pow, one_sub_div hn1, add_sub_cancel_left, pow_succ, div_mul_div_comm, mul_one]
  rw [e] at h
  calc _ ≤ _ := h
    _ = _ := by rw [div_div_eq_mul_div, mul_div_assoc]

/-! ## Problem 11: growth of successive derivatives -/

theorem problem11_sharp (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hf : DifferentiableOn ℂ f (ball z₀ R))
    (s : ℝ) (hs : 0 < s) (hsR : s < R) :
    Tendsto (fun n : ℕ => s ^ n * ‖iteratedDeriv n f z₀‖ / n !) atTop (𝓝 0) := by
  set r := (s + R) / 2
  have hr : 0 < r := by simp only [r]; linarith
  have hsr : s < r := by simp only [r]; linarith
  have hcl : closedBall z₀ r ⊆ ball z₀ R := closedBall_subset_ball (by simp only [r]; linarith)
  have hcont : ContinuousOn f (sphere z₀ r) :=
    hf.continuousOn.mono (sphere_subset_closedBall.trans hcl)
  obtain ⟨M, hM⟩ := (isCompact_sphere z₀ r).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := by
    obtain ⟨w, hw⟩ : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hM w hw)
  have hbound : ∀ n : ℕ, s ^ n * ‖iteratedDeriv n f z₀‖ / n ! ≤ M * (s / r) ^ n := by
    intro n
    have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (hf.diffContOnCl_ball hcl) hM
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hfac, div_pow]
    calc s ^ n * ‖iteratedDeriv n f z₀‖ ≤ s ^ n * (n ! * M / r ^ n) :=
          mul_le_mul_of_nonneg_left hest (by positivity)
      _ = M * (s ^ n / r ^ n) * n ! := by field_simp
  have hlim : Tendsto (fun n : ℕ => M * (s / r) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one hr).mpr hsr)).const_mul M
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => by positivity) hbound

/-- The successive derivatives can never satisfy `|f^(n)(z₀)| > n! nⁿ` for all `n`. -/
theorem problem11 (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) :
    ¬ ∀ n : ℕ, (n ! : ℝ) * n ^ n < ‖iteratedDeriv n f z₀‖ := by
  intro hall
  have hlim := problem11_sharp f z₀ R hf (R / 2) (by linarith) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / R)
  set n := max N₁ N₂
  have h1 := hN₁ n (le_max_left _ _)
  have h2 := hall n
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hnR : 1 ≤ R / 2 * n := by
    have : (N₂ : ℝ) ≤ n := by exact_mod_cast le_max_right N₁ N₂
    rw [div_lt_iff₀ hR] at hN₂
    nlinarith
  have hpow : 1 ≤ (R / 2) ^ n * (n : ℝ) ^ n := by
    rw [← mul_pow]; exact one_le_pow₀ hnR
  rw [div_lt_one hfac] at h1
  have : (R / 2) ^ n * ((n ! : ℝ) * n ^ n) < (R / 2) ^ n * ‖iteratedDeriv n f z₀‖ :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  nlinarith

end HW4
