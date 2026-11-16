import Mathlib

/-!
# Homework 2: analytic functions, partial fractions, power series, exp and log

Formalizations of Homework 2 (Ahlfors, Ch. 2).
-/

open Complex ComplexConjugate Finset Filter Topology Polynomial

noncomputable section

namespace HW2

/-! ## Problem 1: harmonic cubic polynomials -/

section Problem1

/-- The cubic `u(x,y) = a x³ + b x² y + c x y² + d y³`. -/
def u (a b c d : ℝ) (x y : ℝ) : ℝ := a * x ^ 3 + b * x ^ 2 * y + c * x * y ^ 2 + d * y ^ 3

/-- The Laplacian `u_xx + u_yy`, computed with `deriv`. -/
def laplacian (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => deriv (fun t => f t y) s) x + deriv (fun s => deriv (fun t => f x t) s) y

theorem laplacian_u (a b c d x y : ℝ) :
    laplacian (u a b c d) x y = (6 * a + 2 * c) * x + (2 * b + 6 * d) * y := by
  have hx : ∀ s, HasDerivAt (fun t => u a b c d t y) (3 * a * s ^ 2 + 2 * b * y * s + c * y ^ 2) s := by
    intro s
    have h := (((((hasDerivAt_id s).pow 3).const_mul a).add
      ((((hasDerivAt_id s).pow 2).const_mul b).mul_const y)).add
      (((hasDerivAt_id s).const_mul c).mul_const (y ^ 2))).add_const (d * y ^ 3)
    exact h.congr_deriv (by simp; ring)
  have hy : ∀ s, HasDerivAt (fun t => u a b c d x t) (b * x ^ 2 + 2 * c * x * s + 3 * d * s ^ 2) s := by
    intro s
    have h := ((((hasDerivAt_id s).const_mul (b * x ^ 2)).const_add (a * x ^ 3)).add
      (((hasDerivAt_id s).pow 2).const_mul (c * x))).add (((hasDerivAt_id s).pow 3).const_mul d)
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [u] <;> ring
  have hxx : HasDerivAt (fun s => deriv (fun t => u a b c d t y) s) (6 * a * x + 2 * b * y) x := by
    have h := ((((hasDerivAt_id x).pow 2).const_mul (3 * a)).add
      ((hasDerivAt_id x).const_mul (2 * b * y))).add_const (c * y ^ 2)
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    beta_reduce; rw [(hx t).deriv]; simp [Pi.add_apply] <;> ring
  have hyy : HasDerivAt (fun s => deriv (fun t => u a b c d x t) s) (2 * c * x + 6 * d * y) y := by
    have h := (((hasDerivAt_id y).const_mul (2 * c * x)).const_add (b * x ^ 2)).add
      (((hasDerivAt_id y).pow 2).const_mul (3 * d))
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    beta_reduce; rw [(hy t).deriv]; simp [Pi.add_apply] <;> ring
  unfold laplacian; rw [hxx.deriv, hyy.deriv]; ring

/-- `u` is harmonic iff `c = -3a` and `d = -b/3`. -/
theorem problem1_harmonic (a b c d : ℝ) :
    (∀ x y, laplacian (u a b c d) x y = 0) ↔ c = -3 * a ∧ d = -b / 3 := by
  simp only [laplacian_u]
  constructor
  · intro h
    have h1 := h 1 0; have h2 := h 0 1
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩ x y; ring

/-- The analytic function `f(z) = (a - i b/3) z³` has real part `u` and imaginary part `v`,
where `v = 3a x² y + b x y² - a y³ - (b/3) x³` is the harmonic conjugate. -/
theorem problem1_analytic (a b x y : ℝ) :
    (((a : ℂ) - I * b / 3) * (⟨x, y⟩ : ℂ) ^ 3).re = u a b (-3 * a) (-b / 3) x y ∧
    (((a : ℂ) - I * b / 3) * (⟨x, y⟩ : ℂ) ^ 3).im =
      3 * a * x ^ 2 * y + b * x * y ^ 2 - a * y ^ 3 - b / 3 * x ^ 3 := by
  unfold u
  constructor <;> simp [pow_succ] <;> ring

end Problem1

/-! ## Problem 2: analytic with constant modulus ⟹ constant -/

theorem problem2 {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) {C : ℝ} (hC : ∀ z ∈ U, ‖f z‖ = C) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∀ z ∈ U, f z = f z₀ := by
  have hmax : IsMaxOn (norm ∘ f) U z₀ := fun z hz => by
    simp only [Set.mem_setOf_eq, Function.comp, hC z hz, hC z₀ hz₀, le_refl]
  intro z hz
  exact Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hU hf hz₀ hmax hz

/-! ## Problem 3: `f(z)` and `conj (f (conj z))` are simultaneously analytic -/

theorem problem3 (f : ℂ → ℂ) :
    Differentiable ℂ f ↔ Differentiable ℂ (fun z => conj (f (conj z))) := by
  have key : ∀ g : ℂ → ℂ, Differentiable ℂ g → Differentiable ℂ (fun z => conj (g (conj z))) :=
    fun g hg z => by
      have := (hg (conj z)).conj_conj
      simpa [Function.comp_def] using this
  refine ⟨key f, fun h => ?_⟩
  simpa using key _ h

/-! ## Problem 4: Wirtinger derivatives -/

section Problem4

variable (F : ℝ → ℝ → ℂ)

/-- Partial derivatives in `x` and `y`. -/
def dx (x y : ℝ) : ℂ := deriv (fun t => F t y) x
def dy (x y : ℝ) : ℂ := deriv (fun t => F x t) y

/-- Wirtinger derivatives `∂/∂z = ½(∂x - i ∂y)`, `∂/∂z̄ = ½(∂x + i ∂y)`. -/
def dz (x y : ℝ) : ℂ := (dx F x y - I * dy F x y) / 2
def dzbar (x y : ℝ) : ℂ := (dx F x y + I * dy F x y) / 2

/-- `∂²u/∂z∂z̄ = ¼ (u_xx + u_yy)`, assuming the first partials are differentiable and the mixed
partials agree (Schwarz/Clairaut). Hence a harmonic function satisfies `∂²u/∂z∂z̄ = 0`. -/
theorem problem4 (u : ℝ → ℝ → ℂ) (x y : ℝ)
    (hxx : DifferentiableAt ℝ (fun t => dx u t y) x)
    (hyx : DifferentiableAt ℝ (fun t => dy u t y) x)
    (hxy : DifferentiableAt ℝ (fun t => dx u x t) y)
    (hyy : DifferentiableAt ℝ (fun t => dy u x t) y)
    (hsymm : dy (dx u) x y = dx (dy u) x y) :
    dz (dzbar u) x y = (dx (dx u) x y + dy (dy u) x y) / 4 := by
  have e1 : HasDerivAt (fun t => dzbar u t y) ((dx (dx u) x y + I * dx (dy u) x y) / 2) x := by
    unfold dzbar; exact (hxx.hasDerivAt.add (hyx.hasDerivAt.const_mul I)).div_const 2
  have e2 : HasDerivAt (fun t => dzbar u x t) ((dy (dx u) x y + I * dy (dy u) x y) / 2) y := by
    unfold dzbar; exact (hxy.hasDerivAt.add (hyy.hasDerivAt.const_mul I)).div_const 2
  have d1 : dx (dzbar u) x y = (dx (dx u) x y + I * dx (dy u) x y) / 2 := e1.deriv
  have d2 : dy (dzbar u) x y = (dy (dx u) x y + I * dy (dy u) x y) / 2 := e2.deriv
  unfold dz
  rw [d1, d2, hsymm]
  linear_combination (-(dy (dy u) x y) / 4) * I_sq

theorem problem4_harmonic (u : ℝ → ℝ → ℂ) (x y : ℝ)
    (hxx : DifferentiableAt ℝ (fun t => dx u t y) x)
    (hyx : DifferentiableAt ℝ (fun t => dy u t y) x)
    (hxy : DifferentiableAt ℝ (fun t => dx u x t) y)
    (hyy : DifferentiableAt ℝ (fun t => dy u x t) y)
    (hsymm : dy (dx u) x y = dx (dy u) x y)
    (harm : dx (dx u) x y + dy (dy u) x y = 0) :
    dz (dzbar u) x y = 0 := by
  rw [problem4 u x y hxx hyx hxy hyy hsymm, harm, zero_div]

end Problem4

/-! ## Problem 5: partial fractions -/

section Problem5

/-- `ω = e^{2πi/3}` satisfies `ω² + ω + 1 = 0`. -/
theorem omega_sq_add (ω : ℂ) (hω : ω = exp (2 * Real.pi * I / 3)) : ω ^ 2 + ω + 1 = 0 := by
  have hp : IsPrimitiveRoot ω 3 := by rw [hω]; exact_mod_cast isPrimitiveRoot_exp 3 (by norm_num)
  have h3 : ω ^ 3 = 1 := hp.pow_eq_one
  have h1 : ω ≠ 1 := hp.ne_one (by norm_num)
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

theorem problem5_1 (ω z : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (h1 : z ≠ 1) (h2 : z ≠ ω) (h3 : z ≠ ω ^ 2) :
    z ^ 4 / (z ^ 3 - 1) = z + 1 / (3 * (z - 1)) + ω ^ 2 / (3 * (z - ω)) +
      ω / (3 * (z - ω ^ 2)) := by
  have key1 : z ^ 3 - 1 = (z - 1) * (z - ω) * (z - ω ^ 2) := by
    linear_combination ((z - 1) * (z + 1 - ω)) * hω
  have h1' : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : z - ω ≠ 0 := sub_ne_zero.mpr h2
  have h3' : z - ω ^ 2 ≠ 0 := sub_ne_zero.mpr h3
  rw [key1]
  field_simp
  linear_combination (-ω ^ 2 + 2 * z * ω + z * ω ^ 2 - z ^ 2 - 3 * z ^ 2 * ω + 3 * z ^ 3) * hω

theorem problem5_2 (z : ℂ) (h0 : z ≠ 0) (h1 : z + 1 ≠ 0) (h2 : z + 2 ≠ 0) :
    1 / (z * (z + 1) ^ 2 * (z + 2) ^ 3) =
      1 / (8 * z) + 2 / (z + 1) - 1 / (z + 1) ^ 2 - 17 / (8 * (z + 2)) -
        5 / (4 * (z + 2) ^ 2) - 1 / (2 * (z + 2) ^ 3) := by
  field_simp
  ring

end Problem5

/-! ## Problems 6–7: partial fractions with simple poles; Lagrange interpolation -/

section Problem6

open Lagrange

/-- If `Q = ∏ (z - αₖ)` has distinct roots and `deg P < n`, then
`P(z)/Q(z) = ∑ P(αₖ) / (Q'(αₖ) (z - αₖ))`. -/
theorem problem6 {n : ℕ} (α : Fin n → ℂ) (hα : Function.Injective α) (P : ℂ[X])
    (hP : P.degree < n) (z : ℂ) (hz : ∀ k, z ≠ α k) :
    P.eval z / (nodal univ α).eval z =
      ∑ k, P.eval (α k) / ((derivative (nodal univ α)).eval (α k) * (z - α k)) := by
  have hinj : Set.InjOn α (univ : Finset (Fin n)) := hα.injOn
  have hP' : P.degree < (univ : Finset (Fin n)).card := by simpa using hP
  have hQ : (nodal univ α).eval z ≠ 0 := by
    rw [eval_nodal, prod_ne_zero_iff]; intro k _; exact sub_ne_zero.mpr (hz k)
  conv_lhs => rw [eq_interpolate hinj hP']
  rw [eval_interpolate_not_at_node _ (fun k _ => hz k), mul_div_cancel_left₀ _ hQ]
  refine sum_congr rfl fun k _ => ?_
  rw [nodalWeight_eq_eval_derivative_nodal (mem_univ k)]
  field_simp

/-- **Lagrange interpolation**: given distinct nodes `αₖ` and values `cₖ` there is a unique
polynomial of degree `< n` with `P(αₖ) = cₖ`. -/
theorem problem7 {n : ℕ} (α : Fin n → ℂ) (hα : Function.Injective α) (c : Fin n → ℂ) :
    ∃! P : ℂ[X], P.degree < n ∧ ∀ k, P.eval (α k) = c k := by
  have hinj : Set.InjOn α (univ : Finset (Fin n)) := hα.injOn
  refine ⟨interpolate univ α c, ⟨?_, fun k => eval_interpolate_at_node c hinj (mem_univ k)⟩, ?_⟩
  · simpa using degree_interpolate_lt c hinj
  · rintro R ⟨hR, hRc⟩
    refine eq_of_degrees_lt_of_eval_index_eq univ hinj (by simpa using hR)
      (degree_interpolate_lt c hinj) fun k _ => ?_
    rw [hRc k, eval_interpolate_at_node c hinj (mem_univ k)]

/-- The explicit formula `P(z) = ∑ cₖ ∏_{j ≠ k} (z - αⱼ)/(αₖ - αⱼ)`. -/
theorem problem7_formula {n : ℕ} (α : Fin n → ℂ) (c : Fin n → ℂ) (z : ℂ) :
    (interpolate univ α c).eval z =
      ∑ k, c k * ∏ j ∈ univ.erase k, (z - α j) / (α k - α j) := by
  rw [interpolate_apply, eval_finset_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, Lagrange.basis, eval_prod]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C]
  ring

end Problem6

/-! ## Problem 8: `(1 - z)^{-m}` -/

theorem problem8 (m : ℕ) (hm : 1 ≤ m) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((n + m - 1).choose (m - 1) : ℂ) * z ^ n) (1 / (1 - z) ^ m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simpa using hasSum_choose_mul_geometric_of_norm_lt_one k hz

/-! ## Problem 9: `(2z + 3)/(z + 1)` around `z = 1` -/

theorem problem9 {z : ℂ} (hz : ‖z - 1‖ < 2) :
    HasSum (fun n : ℕ => (1 / 2 : ℂ) * (-(z - 1) / 2) ^ n) ((2 * z + 3) / (z + 1) - 2) := by
  have hξ : ‖-(z - 1) / 2‖ < 1 := by
    rw [norm_div, norm_neg]; simp; linarith
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have : z - 1 = -2 := by linear_combination h
    rw [this] at hz; norm_num at hz
  have hz1' : 1 + z ≠ 0 := by rwa [add_comm]
  have := (hasSum_geometric_of_norm_lt_one hξ).mul_left (1 / 2)
  convert this using 1
  rw [show (1 - -(z - 1) / 2 : ℂ) = (z + 1) / 2 by ring, inv_div]
  field_simp
  ring

/-- The radius of convergence is `2`: the series converges iff `|z - 1| < 2`. -/
theorem problem9_radius (z : ℂ) :
    Summable (fun n : ℕ => (1 / 2 : ℂ) * (-(z - 1) / 2) ^ n) ↔ ‖z - 1‖ < 2 := by
  rw [summable_mul_left_iff (by norm_num), summable_geometric_iff_norm_lt_one]
  rw [norm_div, norm_neg]; simp
  constructor <;> intro h <;> linarith

/-! ## Problem 10: radii of convergence (as summability statements) -/

section Problem10

/-- `∑ n^p zⁿ` has radius `1`. -/
theorem problem10_1 (p : ℕ) (z : ℂ) :
    (‖z‖ < 1 → Summable (fun n : ℕ => (n : ℂ) ^ p * z ^ n)) ∧
    (1 < ‖z‖ → ¬ Summable (fun n : ℕ => (n : ℂ) ^ p * z ^ n)) := by
  refine ⟨fun hz => summable_pow_mul_geometric_of_norm_lt_one p hz, fun hz hs => ?_⟩
  have h0 := hs.tendsto_atTop_zero
  have hge : ∀ n : ℕ, 1 ≤ n → 1 ≤ ‖(n : ℂ) ^ p * z ^ n‖ := by
    intro n hn
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast hn))
      (one_le_pow₀ hz.le)
  have := (h0.eventually (Metric.ball_mem_nhds 0 one_pos))
  obtain ⟨N, hN⟩ := eventually_atTop.mp this
  have := hN (N + 1) (by omega)
  rw [dist_zero_right] at this
  linarith [hge (N + 1) (by omega)]

/-- `∑ zⁿ/n!` has radius `∞`. -/
theorem problem10_2 (z : ℂ) : Summable (fun n : ℕ => z ^ n / n.factorial) := by
  exact NormedSpace.expSeries_div_summable z

/-- `∑ n! zⁿ` has radius `0`. -/
theorem problem10_3 (z : ℂ) (hz : z ≠ 0) : ¬ Summable (fun n : ℕ => (n.factorial : ℂ) * z ^ n) := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  -- the ratio `(n+1) |z|` eventually exceeds `2`
  apply not_summable_of_ratio_norm_eventually_ge (r := 2) (by norm_num) _ _ hs
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    have := hN N le_rfl
    simp [Nat.factorial_ne_zero, hz] at this
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 / ‖z‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Nat.factorial_succ, Nat.cast_mul,
      norm_mul, pow_succ, Complex.norm_natCast, Complex.norm_natCast]
    have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have : 2 ≤ ((n + 1 : ℕ) : ℝ) * ‖z‖ := by
      rw [div_lt_iff₀ hz'] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; nlinarith
    have hpos : 0 ≤ (n.factorial : ℝ) * ‖z‖ ^ n := by positivity
    nlinarith

/-- `∑ q^{n²} zⁿ` (`|q| < 1`) has radius `∞`. -/
theorem problem10_4 (q : ℂ) (hq : ‖q‖ < 1) (z : ℂ) :
    Summable (fun n : ℕ => q ^ (n ^ 2) * z ^ n) := by
  -- eventually `|q|ⁿ |z| ≤ 1/2`, so the terms are bounded by `(1/2)ⁿ`
  have hlim : Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖z‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const ‖z‖
  have hev : ∀ᶠ n : ℕ in atTop, ‖q‖ ^ n * ‖z‖ ≤ 1 / 2 :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => (1 / 2 : ℝ) ^ n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with n hn
  rw [norm_mul, norm_pow, norm_pow, sq, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hn n

open Classical in
/-- `∑ z^{n!}`: coefficients `aₘ = 1` if `m` is a factorial, else `0`. Radius `1`. -/
def factorialIndicator (m : ℕ) : ℂ := if ∃ n : ℕ, m = n.factorial then 1 else 0

theorem problem10_5 (z : ℂ) :
    (‖z‖ < 1 → Summable (fun m : ℕ => factorialIndicator m * z ^ m)) ∧
    (1 < ‖z‖ → ¬ Summable (fun m : ℕ => factorialIndicator m * z ^ m)) := by
  constructor
  · intro hz
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun m => ?_
    rw [norm_mul, norm_pow]
    unfold factorialIndicator
    split_ifs <;> simp
  · intro hz hs
    have h0 := hs.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h0.eventually (Metric.ball_mem_nhds 0 one_pos))
    have := hN N.factorial (Nat.self_le_factorial N)
    rw [dist_zero_right] at this
    unfold factorialIndicator at this
    rw [if_pos ⟨N, rfl⟩, one_mul, norm_pow] at this
    linarith [one_le_pow₀ (n := N.factorial) hz.le]

end Problem10

/-! ## Problem 11: radius of `∑ aₙ z^{2n}` and `∑ aₙ² zⁿ` -/

section Problem11

open FormalMultilinearSeries

/-- If `∑ aₙ zⁿ` has radius `R` then `∑ aₙ (z²)ⁿ` converges exactly when `|z|² < R`, i.e. its
radius is `√R`. (Stated through the substitution `w = z²`.) -/
theorem problem11_1 (a : ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hconv : ∀ w : ℂ, ‖w‖ < R → Summable (fun n => a n * w ^ n))
    (hdiv : ∀ w : ℂ, R < ‖w‖ → ¬ Summable (fun n => a n * w ^ n)) (z : ℂ) :
    (‖z‖ < Real.sqrt R → Summable (fun n => a n * z ^ (2 * n))) ∧
    (Real.sqrt R < ‖z‖ → ¬ Summable (fun n => a n * z ^ (2 * n))) := by
  simp_rw [pow_mul]
  constructor
  · intro hz
    apply hconv
    rw [norm_pow]
    calc ‖z‖ ^ 2 < Real.sqrt R ^ 2 := pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
      _ = R := Real.sq_sqrt hR
  · intro hz
    apply hdiv
    rw [norm_pow]
    calc R = Real.sqrt R ^ 2 := (Real.sq_sqrt hR).symm
      _ < ‖z‖ ^ 2 := pow_lt_pow_left₀ hz (Real.sqrt_nonneg R) two_ne_zero

/-- The radius of `∑ aₙ² zⁿ` is the square of the radius of `∑ aₙ zⁿ`
(Cauchy–Hadamard: `limsup |aₙ²|^{1/n} = (limsup |aₙ|^{1/n})²`). -/
theorem problem11_2 (a : ℕ → ℂ) :
    (ofScalars ℂ (fun n => a n ^ 2)).radius = (ofScalars ℂ a).radius ^ 2 := by
  sorry

end Problem11

/-! ## Problem 12: `∑ (z/(1+z))ⁿ` -/

theorem problem12 (z : ℂ) (hz : z ≠ -1) :
    Summable (fun n : ℕ => (z / (1 + z)) ^ n) ↔ -1 / 2 < z.re := by
  rw [summable_geometric_iff_norm_lt_one]
  have h1 : 1 + z ≠ 0 := fun h => hz (by linear_combination h)
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h1), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, add_im, one_re, one_im]
  constructor <;> intro h <;> nlinarith

/-! ## Problem 13: `∑ zⁿ / (1 + z^{2n})` -/

section Problem13

theorem problem13_inside {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n / (1 + z ^ (2 * n))) := by
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => ‖z‖ ^ n / (1 - ‖z‖ ^ 2))
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).div_const _) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpow : ‖z‖ ^ (2 * n) ≤ ‖z‖ ^ 2 :=
    pow_le_pow_of_le_one (norm_nonneg z) hz.le (by omega)
  have hden : 1 - ‖z‖ ^ 2 ≤ ‖1 + z ^ (2 * n)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(z ^ (2 * n)))
    rw [sub_neg_eq_add, norm_neg, norm_one, norm_pow] at this
    linarith
  rw [norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) hden

theorem problem13_outside {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun n : ℕ => z ^ n / (1 + z ^ (2 * n))) := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hw : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  convert problem13_inside hw using 1
  funext n
  have ha : z ^ n ≠ 0 := pow_ne_zero _ hz0
  have e1 : z ^ (2 * n) = (z ^ n) ^ 2 := by ring
  have e2 : z⁻¹ ^ n = (z ^ n)⁻¹ := inv_pow z n
  have e3 : z⁻¹ ^ (2 * n) = ((z ^ n)⁻¹) ^ 2 := by rw [← e2]; ring
  rw [e1, e2, e3]
  generalize z ^ n = a at ha ⊢
  have key : 1 + a⁻¹ ^ 2 = a⁻¹ ^ 2 * (1 + a ^ 2) := by field_simp; ring
  rw [key]
  by_cases h : 1 + a ^ 2 = 0
  · rw [h]; simp
  · field_simp

theorem problem13_circle {z : ℂ} (hz : ‖z‖ = 1) :
    ¬ Summable (fun n : ℕ => z ^ n / (1 + z ^ (2 * n))) := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0.eventually (Metric.ball_mem_nhds 0 (by norm_num :
    (0 : ℝ) < 1 / 2)))
  -- if the denominator is nonzero, the term has modulus `≥ 1/2`
  have big : ∀ n : ℕ, 1 + z ^ (2 * n) ≠ 0 → 1 / 2 ≤ ‖z ^ n / (1 + z ^ (2 * n))‖ := by
    intro n hn
    rw [norm_div, norm_pow, hz, one_pow, le_div_iff₀ (norm_pos_iff.mpr hn)]
    have := norm_add_le (1 : ℂ) (z ^ (2 * n))
    rw [norm_one, norm_pow, hz, one_pow] at this
    linarith
  by_cases hN' : 1 + z ^ (2 * N) = 0
  · -- then `z^{4N} = 1`, so the term at `2N` is fine
    have h2 : 1 + z ^ (2 * (2 * N)) ≠ 0 := by
      have : z ^ (2 * (2 * N)) = (z ^ (2 * N)) ^ 2 := by ring
      rw [this, show z ^ (2 * N) = -1 by linear_combination hN']; norm_num
    have := hN (2 * N) (by omega)
    rw [dist_zero_right] at this
    linarith [big _ h2]
  · have := hN N le_rfl
    rw [dist_zero_right] at this
    linarith [big _ hN']

theorem problem13 (z : ℂ) :
    Summable (fun n : ℕ => z ^ n / (1 + z ^ (2 * n))) ↔ ‖z‖ ≠ 1 := by
  constructor
  · intro hs h; exact problem13_circle h hs
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact problem13_inside h
    · exact problem13_outside h

end Problem13

/-! ## Problem 14: `|cos z|²` and `|sin z|²` -/

section Problem14

theorem cos_xy (x y : ℝ) :
    Complex.cos (x + y * I) =
      (Real.cos x * Real.cosh y : ℝ) + (-(Real.sin x * Real.sinh y) : ℝ) * I := by
  rw [cos_add_mul_I]; push_cast; ring

theorem sin_xy (x y : ℝ) :
    Complex.sin (x + y * I) = (Real.sin x * Real.cosh y : ℝ) + (Real.cos x * Real.sinh y : ℝ) * I := by
  rw [sin_add_mul_I]; push_cast; ring

theorem problem14_cos (x y : ℝ) :
    ‖Complex.cos (x + y * I)‖ ^ 2 = Real.sinh y ^ 2 + Real.cos x ^ 2 ∧
    ‖Complex.cos (x + y * I)‖ ^ 2 = Real.cosh y ^ 2 - Real.sin x ^ 2 ∧
    ‖Complex.cos (x + y * I)‖ ^ 2 = (Real.cosh (2 * y) + Real.cos (2 * x)) / 2 := by
  rw [← normSq_eq_norm_sq, cos_xy, normSq_add_mul_I]
  have h1 := Real.cosh_sq y
  have h2 := Real.sin_sq_add_cos_sq x
  have h3 := Real.cosh_two_mul y
  have h4 := Real.cos_two_mul x
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [h1, h2]
  · nlinarith [h1, h2]
  · rw [h3, h4]; nlinarith [h1, h2]

theorem problem14_sin (x y : ℝ) :
    ‖Complex.sin (x + y * I)‖ ^ 2 = Real.sinh y ^ 2 + Real.sin x ^ 2 ∧
    ‖Complex.sin (x + y * I)‖ ^ 2 = Real.cosh y ^ 2 - Real.cos x ^ 2 ∧
    ‖Complex.sin (x + y * I)‖ ^ 2 = (Real.cosh (2 * y) - Real.cos (2 * x)) / 2 := by
  rw [← normSq_eq_norm_sq, sin_xy, normSq_add_mul_I]
  have h1 := Real.cosh_sq y
  have h2 := Real.sin_sq_add_cos_sq x
  have h3 := Real.cosh_two_mul y
  have h4 := Real.cos_two_mul x
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [h1, h2]
  · nlinarith [h1, h2]
  · rw [h3, h4]; nlinarith [h1, h2]

end Problem14

/-! ## Problem 15: values of `e^z` -/

section Problem15

theorem exp_real_mul_I (θ : ℝ) : exp (θ * I) = Real.cos θ + Real.sin θ * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

theorem problem15_1 : exp (-(Real.pi * I) / 2) = -I := by
  rw [show -(Real.pi * I) / 2 = ((-(Real.pi / 2) : ℝ) : ℂ) * I by push_cast; ring,
    exp_real_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem problem15_2 :
    exp (3 / 4 * Real.pi * I) = -(Real.sqrt 2 / 2) + Real.sqrt 2 / 2 * I := by
  rw [show (3 / 4 * Real.pi * I : ℂ) = ((Real.pi - Real.pi / 4 : ℝ) : ℂ) * I by push_cast; ring,
    exp_real_mul_I, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

theorem problem15_3 :
    exp (2 / 3 * Real.pi * I) = -(1 / 2) + Real.sqrt 3 / 2 * I := by
  rw [show (2 / 3 * Real.pi * I : ℂ) = ((Real.pi - Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring,
    exp_real_mul_I, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

end Problem15

/-! ## Problem 16: solving `e^z = w` -/

section Problem16

/-- Once one solution `z₀` of `e^z = w` is known, all solutions are `z₀ + 2πik`. -/
theorem exp_eq_iff_of_exp_eq {z₀ w : ℂ} (h : exp z₀ = w) (z : ℂ) :
    exp z = w ↔ ∃ k : ℤ, z = z₀ + 2 * Real.pi * I * k := by
  rw [← h, exp_eq_exp_iff_exists_int]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

theorem problem16_1 (z : ℂ) :
    exp z = 2 ↔ ∃ k : ℤ, z = Real.log 2 + 2 * Real.pi * I * k :=
  exp_eq_iff_of_exp_eq (by rw [← ofReal_exp, Real.exp_log (by norm_num)]; norm_num) z

theorem problem16_2 (z : ℂ) :
    exp z = -1 ↔ ∃ k : ℤ, z = (2 * k + 1) * Real.pi * I := by
  rw [exp_eq_iff_of_exp_eq exp_pi_mul_I]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

theorem problem16_3 (z : ℂ) :
    exp z = I ↔ ∃ k : ℤ, z = I * (Real.pi / 2 + 2 * Real.pi * k) := by
  have h : exp (Real.pi / 2 * I) = I := by
    rw [show (Real.pi / 2 * I : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_real_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  rw [exp_eq_iff_of_exp_eq h]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

theorem problem16_4 (z : ℂ) :
    exp z = -I / 2 ↔ ∃ k : ℤ, z = -Real.log 2 + I * (-(Real.pi / 2) + 2 * Real.pi * k) := by
  have h : exp (-Real.log 2 + -(Real.pi / 2) * I) = -I / 2 := by
    rw [exp_add, show (-(Real.pi / 2) * I : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * I by push_cast; ring,
      exp_real_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
      ← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
    push_cast; ring
  rw [exp_eq_iff_of_exp_eq h]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

theorem problem16_5 (z : ℂ) :
    exp z = -1 - I ↔
      ∃ k : ℤ, z = 1 / 2 * Real.log 2 + I * (-(3 * Real.pi / 4) + 2 * Real.pi * k) := by
  have hs : Real.exp (1 / 2 * Real.log 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]; ring_nf
  have h : exp (1 / 2 * Real.log 2 + -(3 * Real.pi / 4) * I) = -1 - I := by
    rw [exp_add, show (-(3 * Real.pi / 4) * I : ℂ) =
        ((-(Real.pi - Real.pi / 4)) : ℝ) * I by push_cast; ring,
      exp_real_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_four, Real.sin_pi_div_four,
      show (1 / 2 * Real.log 2 : ℂ) = ((1 / 2 * Real.log 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, hs]
    have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
      rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    push_cast
    linear_combination (-1 / 2 - I / 2) * h2
  rw [exp_eq_iff_of_exp_eq h]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

theorem problem16_6 (z : ℂ) :
    exp z = 1 + 2 * I ↔
      ∃ k : ℤ, z = 1 / 2 * Real.log 5 + I * (Real.arctan 2 + 2 * Real.pi * k) := by
  have hs : Real.exp (1 / 2 * Real.log 5) = Real.sqrt 5 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]; ring_nf
  have h5 : Real.sqrt (1 + 2 ^ 2) = Real.sqrt 5 := by norm_num
  have hpos : 0 < Real.sqrt 5 := by positivity
  have h : exp (1 / 2 * Real.log 5 + Real.arctan 2 * I) = 1 + 2 * I := by
    rw [exp_add, exp_real_mul_I, Real.cos_arctan, Real.sin_arctan, h5,
      show (1 / 2 * Real.log 5 : ℂ) = ((1 / 2 * Real.log 5 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, hs]
    have : (Real.sqrt 5 : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
  rw [exp_eq_iff_of_exp_eq h]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by rw [hk]; ring⟩

end Problem16

/-! ## Problem 17: all values of `2^i`, `i^i`, `(-1)^{2i}` -/

section Problem17

/-- The values of `z^w = e^{w log z}` run over all branches `log z + 2πik`. -/
theorem problem17_1 (k : ℤ) :
    exp (I * (Real.log 2 + 2 * Real.pi * I * k)) =
      Real.exp (-2 * Real.pi * k) * exp (I * Real.log 2) := by
  rw [ofReal_exp, ← exp_add]; congr 1; push_cast
  linear_combination (2 * (Real.pi : ℂ) * k) * I_sq

theorem problem17_2 (k : ℤ) :
    exp (I * (I * (Real.pi / 2 + 2 * Real.pi * k))) =
      Real.exp (-(Real.pi / 2) - 2 * Real.pi * k) := by
  rw [ofReal_exp]; congr 1; push_cast
  linear_combination ((Real.pi : ℂ) / 2 + 2 * Real.pi * k) * I_sq

theorem problem17_3 (k : ℤ) :
    exp (2 * I * (I * (Real.pi + 2 * Real.pi * k))) =
      Real.exp (-2 * Real.pi - 4 * Real.pi * k) := by
  rw [ofReal_exp]; congr 1; push_cast
  linear_combination (2 * ((Real.pi : ℂ) + 2 * Real.pi * k)) * I_sq

/-- The principal value `i^i = e^{-π/2}` agrees with Mathlib's `cpow`. -/
theorem problem17_principal : (I : ℂ) ^ I = Real.exp (-(Real.pi / 2)) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I, ofReal_exp]
  congr 1; push_cast
  linear_combination ((Real.pi : ℂ) / 2) * I_sq

end Problem17

end HW2
