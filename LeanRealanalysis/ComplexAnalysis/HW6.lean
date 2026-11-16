import Mathlib

/-!
# Homework 6: sequences of analytic functions, Taylor and Laurent series

Formalizations of Homework 6 (Ahlfors, Ch. 5).
-/

open Complex ComplexConjugate Filter Topology Metric Set
open scoped Nat

noncomputable section

namespace HW6

/-! ## Problem 1: `(1 + z/n)ⁿ → eᶻ` uniformly on compact sets -/

/-- `|aⁿ - bⁿ| ≤ n |a - b| M^{n-1}` when `|a|, |b| ≤ M`. -/
theorem norm_pow_sub_pow_le' (a b : ℂ) (M : ℝ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ * M ^ (n - 1) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  rw [← geom_sum₂_mul, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖ ≤ n * M ^ (n - 1) := by
    calc ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖
        ≤ ∑ i ∈ Finset.range n, ‖a ^ i * b ^ (n - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, M ^ (n - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, norm_pow, norm_pow,
            show M ^ (n - 1) = M ^ i * M ^ (n - 1 - i) by rw [← pow_add]; congr 1; omega]
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha i)
            (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
      _ = n * M ^ (n - 1) := by simp
  calc ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖ * ‖a - b‖
      ≤ n * M ^ (n - 1) * ‖a - b‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = n * ‖a - b‖ * M ^ (n - 1) := by ring

theorem problem1 :
    TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => (1 + z / n) ^ n) exp atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  set R' := max R 1
  have hR'1 : 1 ≤ R' := le_max_right _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (R' ^ 2 * Real.exp R' / ε + R')
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < R' ^ 2 * Real.exp R' / ε := by positivity
  have hnR : R' < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hzR : ‖z‖ ≤ R' := by
    have := hR hz; rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set w := z / n
  have hw : ‖w‖ = ‖z‖ / n := by simp [w, norm_div]
  have hw1 : ‖w‖ ≤ 1 := by rw [hw, div_le_one hn0]; linarith
  have hexp : exp z = exp w ^ n := by
    rw [← exp_nat_mul]; congr 1; simp only [w]; field_simp
  have hab : ‖exp w - (1 + w)‖ ≤ ‖w‖ ^ 2 := by
    rw [show exp w - (1 + w) = exp w - 1 - w by ring]; exact norm_exp_sub_one_sub_id_le hw1
  have ha : ‖exp w‖ ≤ Real.exp ‖w‖ := norm_exp_le_exp_norm w
  have hb : ‖1 + w‖ ≤ Real.exp ‖w‖ := by
    calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = ‖w‖ + 1 := by rw [norm_one]; ring
      _ ≤ Real.exp ‖w‖ := Real.add_one_le_exp _
  have hkey := norm_pow_sub_pow_le' (exp w) (1 + w) _ ha hb n
  have hMpow : Real.exp ‖w‖ ^ (n - 1) ≤ Real.exp R' := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hw]
    calc ((n - 1 : ℕ) : ℝ) * (‖z‖ / n) ≤ n * (‖z‖ / n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le n 1
      _ = ‖z‖ := by field_simp
      _ ≤ R' := hzR
  rw [dist_eq_norm, hexp]
  calc ‖exp w ^ n - (1 + w) ^ n‖ ≤ n * ‖exp w - (1 + w)‖ * Real.exp ‖w‖ ^ (n - 1) := hkey
    _ ≤ n * ‖w‖ ^ 2 * Real.exp R' := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hab (by positivity)) hMpow
          (by positivity) (by positivity)
    _ = ‖z‖ ^ 2 * Real.exp R' / n := by rw [hw]; field_simp
    _ ≤ R' ^ 2 * Real.exp R' / n := by
        apply div_le_div_of_nonneg_right _ hn0.le
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzR 2) (by positivity)
    _ < ε := by
        have h : R' ^ 2 * Real.exp R' / ε < n := by linarith
        rw [div_lt_iff₀ hε] at h
        rw [div_lt_iff₀ hn0]; linarith

/-- The pointwise statement (Mathlib). -/
theorem problem1_pointwise (z : ℂ) : Tendsto (fun n : ℕ => (1 + z / n) ^ n) atTop (𝓝 (exp z)) :=
  tendsto_one_add_div_pow_exp z

/-! ## Problem 2: `ζ(z) = ∑ n^{-z}` -/

theorem problem2_summable (z : ℂ) (hz : 1 < z.re) : Summable (fun n : ℕ => 1 / (n : ℂ) ^ z) :=
  Complex.summable_one_div_nat_cpow.mpr hz

/-- Term-by-term differentiation: `ζ'(z) = -∑ (log n) n^{-z}` for `Re z > 1`. -/
theorem problem2_deriv (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun z => ∑' n : ℕ, 1 / (n : ℂ) ^ z) (-∑' n : ℕ, log n / (n : ℂ) ^ s) s := by
  have habs : LSeries.abscissaOfAbsConv 1 < (s.re : EReal) := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have h := LSeries_hasDerivAt habs
  -- identify `LSeries 1` with `∑ n^{-z}` near `s` (they agree whenever `z ≠ 0`)
  have hterm : ∀ z : ℂ, z ≠ 0 → LSeries 1 z = ∑' n : ℕ, 1 / (n : ℂ) ^ z := by
    intro z hz
    unfold LSeries
    congr 1; funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · subst hn; simp [zero_cpow hz]
    · simp
  have hlog : LSeries (LSeries.logMul 1) s = ∑' n : ℕ, log n / (n : ℂ) ^ s := by
    unfold LSeries
    congr 1; funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · subst hn; simp
    · simp only [LSeries.logMul, Pi.one_apply, mul_one]
  rw [hlog] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hs0] with z hz
  exact (hterm z hz).symm

/-! ## Problem 3: limits of functions with at most `m` zeros -/

/-- If `fₙ → f` locally uniformly on a region `Ω` and each `fₙ` has at most `m` zeros in `Ω`,
then `f` is identically zero or has at most `m` zeros. -/
theorem problem3 (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : IsConnected Ω) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hlim : TendstoLocallyUniformlyOn F f atTop Ω)
    (m : ℕ) (hzeros : ∀ n, (Ω ∩ F n ⁻¹' {0}).encard ≤ m) :
    (∀ z ∈ Ω, f z = 0) ∨ (Ω ∩ f ⁻¹' {0}).encard ≤ m := by
  sorry

/-! ## Problem 4: `1/(1 + z²)` in powers of `z - a` -/

section Problem4

/-- The Taylor coefficients of `1/(1+z²)` at the real point `a`. -/
def c (a : ℝ) (n : ℕ) : ℂ := (-1) ^ n / (2 * I) * (1 / (a - I) ^ (n + 1) - 1 / (a + I) ^ (n + 1))

/-- Geometric expansion of `1/(z - w)` around `a`. -/
theorem hasSum_inv_sub (a z w : ℂ) (h : ‖z - a‖ < ‖w - a‖) :
    HasSum (fun n : ℕ => -(z - a) ^ n / (w - a) ^ (n + 1)) (1 / (z - w)) := by
  have hwa : w - a ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact absurd h (not_lt.mpr (norm_nonneg _))
  have hξ : ‖(z - a) / (w - a)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hwa)]; exact h
  have hzw : z - w ≠ 0 := by
    intro h0; rw [show z - a = w - a by linear_combination h0] at h; exact lt_irrefl _ h
  have := (hasSum_geometric_of_norm_lt_one hξ).mul_left (-1 / (w - a))
  convert this using 1
  · funext n; rw [div_pow, pow_succ]; field_simp
  · have hwz : w - z ≠ 0 := fun h0 => hzw (by linear_combination -h0)
    rw [one_sub_div hwa, inv_div, show w - a - (z - a) = w - z by ring]
    field_simp
    ring

theorem neg_one_pow_div (x : ℂ) (hx : x ≠ 0) (n : ℕ) :
    (-1 : ℂ) ^ n / x ^ (n + 1) = -1 / (-x) ^ (n + 1) := by
  have hsq : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hx' : (-x) ^ (n + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hx)
  rw [div_eq_div_iff (pow_ne_zero _ hx) hx', neg_pow x (n + 1), pow_succ (-1 : ℂ) n]
  linear_combination (-(x ^ (n + 1))) * hsq

theorem problem4 (a : ℝ) (z : ℂ) (hz : ‖z - a‖ < Real.sqrt (a ^ 2 + 1)) :
    HasSum (fun n : ℕ => c a n * (z - a) ^ n) (1 / (1 + z ^ 2)) := by
  have hIa : ‖I - (a : ℂ)‖ = Real.sqrt (a ^ 2 + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← normSq_eq_norm_sq]
    congr 1; simp [normSq_apply]; ring
  have hmIa : ‖-I - (a : ℂ)‖ = Real.sqrt (a ^ 2 + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← normSq_eq_norm_sq]
    congr 1; simp [normSq_apply]; ring
  have h1 := hasSum_inv_sub a z I (by rw [hIa]; exact hz)
  have h2 := hasSum_inv_sub a z (-I) (by rw [hmIa]; exact hz)
  have hz1 : z - I ≠ 0 := by
    intro h0; rw [sub_eq_zero.mp h0, hIa] at hz; exact lt_irrefl _ hz
  have hz2 : z + I ≠ 0 := by
    intro h0; rw [show z = -I by linear_combination h0, hmIa] at hz; exact lt_irrefl _ hz
  have key := (h1.sub h2).mul_left (1 / (2 * I))
  have hval : 1 / (2 * I) * (1 / (z - I) - 1 / (z - -I)) = 1 / (1 + z ^ 2) := by
    have h3 : 1 + z ^ 2 = (z - I) * (z + I) := by linear_combination I_sq
    rw [h3, sub_neg_eq_add]
    field_simp
    ring
  rw [hval] at key
  convert key using 1
  funext n
  have ha1 : (a : ℂ) - I ≠ 0 := by
    intro h0; have := congrArg im h0; simp at this
  have ha2 : (a : ℂ) + I ≠ 0 := by
    intro h0; have := congrArg im h0; simp at this
  have kc : c a n = 1 / (2 * I) * ((-1) ^ n / ((a : ℂ) - I) ^ (n + 1) -
      (-1) ^ n / ((a : ℂ) + I) ^ (n + 1)) := by unfold c; ring
  rw [kc, neg_one_pow_div _ ha1, neg_one_pow_div _ ha2, show -((a : ℂ) - I) = I - a by ring,
    show -((a : ℂ) + I) = -I - a by ring]
  ring

/-- For `a = 1` the coefficients satisfy `c_{n+4} = -c_n/4`, with `c₀, …, c₃ = 1/2, -1/2, 1/4, 0`. -/
theorem problem4_a1 :
    c 1 0 = 1 / 2 ∧ c 1 1 = -1 / 2 ∧ c 1 2 = 1 / 4 ∧ c 1 3 = 0 ∧
      ∀ n, c 1 (n + 4) = -c 1 n / 4 := by
  have p1 : (((1 : ℝ) : ℂ) - I) ^ 4 = -4 := by
    apply Complex.ext <;> simp [pow_succ] <;> norm_num
  have p2 : (((1 : ℝ) : ℂ) + I) ^ 4 = -4 := by
    apply Complex.ext <;> simp [pow_succ] <;> norm_num
  have h1 : ((1 : ℝ) : ℂ) - I ≠ 0 := by intro h0; have := congrArg im h0; simp at this
  have h2 : ((1 : ℝ) : ℂ) + I ≠ 0 := by intro h0; have := congrArg im h0; simp at this
  refine ⟨?_, ?_, ?_, ?_, fun n => ?_⟩
  · apply Complex.ext <;> simp [c, pow_succ, Complex.div_re, Complex.div_im, normSq_apply] <;>
      norm_num
  · apply Complex.ext <;> simp [c, pow_succ, Complex.div_re, Complex.div_im, normSq_apply] <;>
      norm_num
  · apply Complex.ext <;> simp [c, pow_succ, Complex.div_re, Complex.div_im, normSq_apply] <;>
      norm_num
  · unfold c; rw [show (3 + 1 : ℕ) = 4 from rfl, p1, p2]; ring
  · have e1 : (((1 : ℝ) : ℂ) - I) ^ (n + 4 + 1) = (((1 : ℝ) : ℂ) - I) ^ (n + 1) * (-4) := by
      rw [show n + 4 + 1 = (n + 1) + 4 by ring, pow_add, p1]
    have e2 : (((1 : ℝ) : ℂ) + I) ^ (n + 4 + 1) = (((1 : ℝ) : ℂ) + I) ^ (n + 1) * (-4) := by
      rw [show n + 4 + 1 = (n + 1) + 4 by ring, pow_add, p2]
    unfold c
    rw [e1, e2, show (-1 : ℂ) ^ (n + 4) = (-1) ^ n by rw [pow_add]; norm_num]
    have : (((1 : ℝ) : ℂ) - I) ^ (n + 1) ≠ 0 := pow_ne_zero _ h1
    have : (((1 : ℝ) : ℂ) + I) ^ (n + 1) ≠ 0 := pow_ne_zero _ h2
    field_simp
    ring

end Problem4

/-! ## Problem 5: `log(sin z / z)` up to `z⁶` -/

theorem problem5 :
    (fun z : ℂ => log (sin z / z) - (-z ^ 2 / 6 - z ^ 4 / 180 - z ^ 6 / 2835)) =O[𝓝 0]
      (fun z => z ^ 8) := by
  sorry

/-! ## Problem 6: the coefficient of `z⁷` in `tan z` is `17/315` -/

/-- Solving `tan z · cos z = sin z` order by order: with `tan z = az + bz³ + cz⁵ + dz⁷ + ⋯`,
the triangular system has the solution `a = 1, b = 1/3, c = 2/15, d = 17/315`. -/
theorem problem6_system :
    let a : ℚ := 1; let b : ℚ := 1 / 3; let c : ℚ := 2 / 15; let d : ℚ := 17 / 315
    a = 1 ∧ b - a / 2 = -1 / 6 ∧ c - b / 2 + a / 24 = 1 / 120 ∧
      d - c / 2 + b / 24 - a / 720 = -1 / 5040 := by
  norm_num

theorem problem6 : iteratedDeriv 7 Complex.tan 0 / (7 ! : ℂ) = 17 / 315 := by
  sorry

/-! ## Problem 7: the Schwarzian derivative at a multiple zero or pole -/

section Problem7

/-- The Schwarzian derivative `{f, z} = f'''/f' - (3/2)(f''/f')²`. -/
def schwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 3 f z / deriv f z - 3 / 2 * (iteratedDeriv 2 f z / deriv f z) ^ 2

/-- The leading-term computation: if `f'`, `f''`, `f'''` have leading terms
`a m wᵐ⁻¹`, `a m(m-1) wᵐ⁻²`, `a m(m-1)(m-2) wᵐ⁻³` (`w = z - z₀`), then the leading term of
`{f, z}` is `(1 - m²)/(2w²)`. -/
theorem problem7_leading (a w : ℂ) (m : ℤ) (ha : a ≠ 0) (hw : w ≠ 0) (hm : (m : ℂ) ≠ 0) :
    let f1 := a * m * w ^ (m - 1)
    let f2 := a * m * (m - 1) * w ^ (m - 2)
    let f3 := a * m * (m - 1) * (m - 2) * w ^ (m - 3)
    f3 / f1 - 3 / 2 * (f2 / f1) ^ 2 = (1 - m ^ 2) / (2 * w ^ 2) := by
  intro f1 f2 f3
  have e2 : w ^ (m - 2) = w ^ (m - 1) / w := by
    rw [show m - 2 = (m - 1) - 1 by ring, zpow_sub₀ hw, zpow_one]
  have e3 : w ^ (m - 3) = w ^ (m - 1) / w ^ 2 := by
    rw [show m - 3 = (m - 1) - 2 by ring, zpow_sub₀ hw]; norm_cast
  have hp : w ^ (m - 1) ≠ 0 := zpow_ne_zero _ hw
  simp only [f1, f2, f3, e2, e3]
  field_simp
  ring

/-- The full statement: if `f` has a zero or pole of order `m` (`|m| ≥ 2`) at `z₀`, then
`{f, z} = (1 - m²)/(2 (z - z₀)²) + O((z - z₀)⁻¹)`. -/
theorem problem7 (f : ℂ → ℂ) (z₀ : ℂ) (m : ℤ) (hm : 2 ≤ |m|) (hf : MeromorphicAt f z₀)
    (hord : meromorphicOrderAt f z₀ = m) :
    (fun z => schwarzian f z - (1 - m ^ 2) / (2 * (z - z₀) ^ 2)) =O[𝓝[≠] z₀]
      (fun z => (z - z₀)⁻¹) := by
  sorry

end Problem7

/-! ## Problem 8: `1/(eᶻ - 1)` and the Bernoulli numbers -/

section Problem8

open PowerSeries

/-- Ahlfors's Bernoulli numbers: `B_k = (-1)^(k-1) bernoulli (2k)` (all positive). -/
def B (k : ℕ) : ℚ := (-1) ^ (k - 1) * bernoulli (2 * k)

/-- The generating function: `z/(eᶻ - 1) = ∑ bernoulli n zⁿ/n!` as formal power series. -/
theorem problem8_series : bernoulliPowerSeries ℚ * (exp ℚ - 1) = X :=
  bernoulliPowerSeries_mul_exp_sub_one ℚ

/-- The odd coefficients: `-1/2` for `z¹`, zero for `z³, z⁵, …`; so
`1/(eᶻ - 1) = 1/z - 1/2 + ∑ (-1)^(k-1) B_k/(2k)! z^(2k-1)`. -/
theorem problem8_odd : bernoulli 1 = -1 / 2 ∧ ∀ k, 1 ≤ k → bernoulli (2 * k + 1) = 0 :=
  ⟨bernoulli_one, fun k hk => bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)⟩

theorem bernoulli'_five : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_five, Nat.choose]

/-- `B₁ = 1/6`, `B₂ = 1/30`, `B₃ = 1/42`. -/
theorem problem8_values : B 1 = 1 / 6 ∧ B 2 = 1 / 30 ∧ B 3 = 1 / 42 := by
  unfold B
  refine ⟨?_, ?_, ?_⟩
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]; norm_num [bernoulli'_two]
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]; norm_num [bernoulli'_four]
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]; norm_num [bernoulli'_six]

/-- The coefficients found in the solution: `a = B₁/2! = 1/12`, `b = -B₂/4! = -1/720`,
`c = B₃/6! = 1/30240`. -/
theorem problem8_coeffs :
    B 1 / 2 ! = 1 / 12 ∧ -B 2 / 4 ! = -1 / 720 ∧ B 3 / 6 ! = 1 / 30240 := by
  obtain ⟨h1, h2, h3⟩ := problem8_values
  rw [h1, h2, h3]
  norm_num [Nat.factorial]

end Problem8

end HW6
