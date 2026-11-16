import Mathlib

/-!
# Homework 1: complex numbers

Formalizations of Homework 1 (Ahlfors, Ch. 1).
-/

open Complex ComplexConjugate Finset

noncomputable section

namespace HW1

/-! ## Problem 1: real and imaginary parts -/

section Problem1

variable (x y : ℝ)

theorem problem1_1 :
    ((⟨x, y⟩ : ℂ) ^ 4).re = x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4 ∧
    ((⟨x, y⟩ : ℂ) ^ 4).im = 4 * x * y * (x ^ 2 - y ^ 2) := by
  constructor <;> simp [pow_succ] <;> ring

theorem problem1_2 :
    (1 / (⟨x, y⟩ : ℂ)).re = x / (x ^ 2 + y ^ 2) ∧
    (1 / (⟨x, y⟩ : ℂ)).im = -y / (x ^ 2 + y ^ 2) := by
  constructor <;> simp [Complex.div_re, Complex.div_im, normSq_apply] <;> ring

theorem problem1_3 :
    (((⟨x, y⟩ : ℂ) - 1) / ((⟨x, y⟩ : ℂ) + 1)).re = (x ^ 2 + y ^ 2 - 1) / ((x + 1) ^ 2 + y ^ 2) ∧
    (((⟨x, y⟩ : ℂ) - 1) / ((⟨x, y⟩ : ℂ) + 1)).im = 2 * y / ((x + 1) ^ 2 + y ^ 2) := by
  constructor <;> simp [Complex.div_re, Complex.div_im, normSq_apply] <;> ring

theorem problem1_4 :
    (1 / (⟨x, y⟩ : ℂ) ^ 2).re = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 ∧
    (1 / (⟨x, y⟩ : ℂ) ^ 2).im = -(2 * x * y) / (x ^ 2 + y ^ 2) ^ 2 := by
  obtain ⟨h1, h2⟩ := problem1_2 x y
  rw [← one_div_pow, pow_two]
  simp only [mul_re, mul_im, h1, h2]
  generalize x ^ 2 + y ^ 2 = s
  constructor <;> ring

end Problem1

/-! ## Problems 2–3: square roots and fourth roots -/

section Problem2

/-- `exp (θ i)` for real `θ` in rectangular form. -/
theorem exp_real_mul_I (θ : ℝ) : exp (θ * I) = Real.cos θ + Real.sin θ * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

theorem exp_mul_I_pow (θ : ℝ) (n : ℕ) : exp (θ * I) ^ n = exp ((n * θ : ℝ) * I) := by
  rw [← exp_nat_mul]; push_cast; ring_nf

/-- The square roots of `w` are `±` any one of them. -/
theorem sq_eq_iff {w a : ℂ} : w ^ 2 = a ^ 2 ↔ w = a ∨ w = -a := sq_eq_sq_iff_eq_or_eq_neg

theorem exp_add_pi (θ : ℝ) : exp ((θ + Real.pi : ℝ) * I) = -exp (θ * I) := by
  push_cast; rw [add_mul, exp_add, exp_pi_mul_I]; ring

theorem problem2_1 (w : ℂ) :
    w ^ 2 = I ↔ w = exp ((Real.pi / 4 : ℝ) * I) ∨ w = exp ((5 * Real.pi / 4 : ℝ) * I) := by
  have h5 : exp ((5 * Real.pi / 4 : ℝ) * I) = -exp ((Real.pi / 4 : ℝ) * I) := by
    rw [← exp_add_pi]; congr 3; ring
  have hsq : exp ((Real.pi / 4 : ℝ) * I) ^ 2 = I := by
    rw [exp_mul_I_pow, exp_real_mul_I]
    have : ((2 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi / 2 := by push_cast; ring
    rw [this, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  rw [h5, ← sq_eq_iff, hsq]

theorem problem2_2 (w : ℂ) :
    w ^ 2 = -I ↔ w = exp ((3 * Real.pi / 4 : ℝ) * I) ∨ w = exp ((7 * Real.pi / 4 : ℝ) * I) := by
  have h7 : exp ((7 * Real.pi / 4 : ℝ) * I) = -exp ((3 * Real.pi / 4 : ℝ) * I) := by
    rw [← exp_add_pi]; congr 3; ring
  have hsq : exp ((3 * Real.pi / 4 : ℝ) * I) ^ 2 = -I := by
    rw [exp_mul_I_pow, exp_real_mul_I]
    have : ((2 : ℕ) : ℝ) * (3 * Real.pi / 4) = Real.pi / 2 + Real.pi := by push_cast; ring
    rw [this, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  rw [h7, ← sq_eq_iff, hsq]

theorem problem2_3 (w : ℂ) :
    w ^ 2 = 1 + I ↔
      w = (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * exp ((Real.pi / 8 : ℝ) * I) ∨
      w = (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * exp ((9 * Real.pi / 8 : ℝ) * I) := by
  have h9 : exp ((9 * Real.pi / 8 : ℝ) * I) = -exp ((Real.pi / 8 : ℝ) * I) := by
    rw [← exp_add_pi]; congr 3; ring
  have h2 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow]; norm_num
  have hsq : ((((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * exp ((Real.pi / 8 : ℝ) * I) : ℂ) ^ 2 = 1 + I := by
    rw [mul_pow, exp_mul_I_pow, exp_real_mul_I, ← ofReal_pow, h2]
    have : ((2 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 4 := by push_cast; ring
    rw [this, Real.cos_pi_div_four, Real.sin_pi_div_four]
    apply Complex.ext <;> simp <;>
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h9, mul_neg, ← sq_eq_iff, hsq]

theorem problem2_4 (w : ℂ) :
    w ^ 2 = (1 - Real.sqrt 3 * I) / 2 ↔
      w = exp ((5 * Real.pi / 6 : ℝ) * I) ∨ w = exp ((11 * Real.pi / 6 : ℝ) * I) := by
  have h11 : exp ((11 * Real.pi / 6 : ℝ) * I) = -exp ((5 * Real.pi / 6 : ℝ) * I) := by
    rw [← exp_add_pi]; congr 3; ring
  have hsq : exp ((5 * Real.pi / 6 : ℝ) * I) ^ 2 = (1 - Real.sqrt 3 * I) / 2 := by
    rw [exp_mul_I_pow, exp_real_mul_I]
    have : ((2 : ℕ) : ℝ) * (5 * Real.pi / 6) = -(Real.pi / 3) + 2 * Real.pi := by push_cast; ring
    rw [this, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    apply Complex.ext <;> simp <;> ring
  rw [h11, ← sq_eq_iff, hsq]

end Problem2

section Problem3

/-- The fourth roots of `a ^ 4` are `a, i a, -a, -i a`. -/
theorem pow_four_eq_iff {w a : ℂ} :
    w ^ 4 = a ^ 4 ↔ w = a ∨ w = I * a ∨ w = -a ∨ w = -(I * a) := by
  have key : w ^ 4 - a ^ 4 = (w - a) * (w - I * a) * (w + a) * (w + I * a) := by
    linear_combination ((w ^ 2 - a ^ 2) * a ^ 2) * I_sq
  rw [← sub_eq_zero, key]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

theorem I_mul_exp (θ : ℝ) : I * exp (θ * I) = exp ((θ + Real.pi / 2 : ℝ) * I) := by
  push_cast; rw [add_mul, exp_add, ← ofReal_ofNat, ← ofReal_div,
    exp_real_mul_I (Real.pi / 2), Real.cos_pi_div_two, Real.sin_pi_div_two]; simp; ring

theorem problem3_1 (w : ℂ) :
    w ^ 4 = I ↔ w = exp ((Real.pi / 8 : ℝ) * I) ∨ w = exp ((5 * Real.pi / 8 : ℝ) * I) ∨
      w = exp ((9 * Real.pi / 8 : ℝ) * I) ∨ w = exp ((13 * Real.pi / 8 : ℝ) * I) := by
  set a := exp ((Real.pi / 8 : ℝ) * I)
  have ha : a ^ 4 = I := by
    rw [exp_mul_I_pow, exp_real_mul_I]
    have : ((4 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 2 := by push_cast; ring
    rw [this, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  have h5 : exp ((5 * Real.pi / 8 : ℝ) * I) = I * a := by
    rw [I_mul_exp]; congr 3; ring
  have h9 : exp ((9 * Real.pi / 8 : ℝ) * I) = -a := by
    rw [← exp_add_pi]; congr 3; ring
  have h13 : exp ((13 * Real.pi / 8 : ℝ) * I) = -(I * a) := by
    rw [← h5, ← exp_add_pi]; congr 3; ring
  rw [h5, h9, h13, show w ^ 4 = I ↔ w ^ 4 = a ^ 4 by rw [ha]]; exact pow_four_eq_iff

theorem problem3_2 (w : ℂ) :
    w ^ 4 = -I ↔ w = exp ((-Real.pi / 8 : ℝ) * I) ∨ w = exp ((3 * Real.pi / 8 : ℝ) * I) ∨
      w = exp ((7 * Real.pi / 8 : ℝ) * I) ∨ w = exp ((11 * Real.pi / 8 : ℝ) * I) := by
  set a := exp ((-Real.pi / 8 : ℝ) * I)
  have ha : a ^ 4 = -I := by
    rw [exp_mul_I_pow, exp_real_mul_I]
    have : ((4 : ℕ) : ℝ) * (-Real.pi / 8) = -(Real.pi / 2) := by push_cast; ring
    rw [this, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  have h3 : exp ((3 * Real.pi / 8 : ℝ) * I) = I * a := by
    rw [I_mul_exp]; congr 3; ring
  have h7 : exp ((7 * Real.pi / 8 : ℝ) * I) = -a := by
    rw [← exp_add_pi]; congr 3; ring
  have h11 : exp ((11 * Real.pi / 8 : ℝ) * I) = -(I * a) := by
    rw [← h3, ← exp_add_pi]; congr 3; ring
  rw [h3, h7, h11, show w ^ 4 = -I ↔ w ^ 4 = a ^ 4 by rw [ha]]; exact pow_four_eq_iff

end Problem3

/-! ## Problem 4 -/

section Problem4

/-- Key identity: `|1 - ā b|² - |a - b|² = (1 - |a|²)(1 - |b|²)`. -/
theorem normSq_one_sub_conj_mul_sub (a b : ℂ) :
    normSq (1 - conj a * b) - normSq (a - b) = (1 - normSq a) * (1 - normSq b) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

/-- If `|a| = 1` or `|b| = 1` (and `ā b ≠ 1`), then `|(a - b) / (1 - ā b)| = 1`. -/
theorem problem4 (a b : ℂ) (hab : ‖a‖ = 1 ∨ ‖b‖ = 1) (hden : 1 - conj a * b ≠ 0) :
    ‖(a - b) / (1 - conj a * b)‖ = 1 := by
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  have h := normSq_one_sub_conj_mul_sub a b
  have h0 : (1 - normSq a) * (1 - normSq b) = 0 := by
    rcases hab with h1 | h1 <;> simp [normSq_eq_norm_sq, h1]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  linarith

/-- The exception: when `|a| = |b| = 1` the expression is undefined exactly when `a = b`. -/
theorem problem4_exception (a b : ℂ) (ha : ‖a‖ = 1) :
    1 - conj a * b = 0 ↔ a = b := by
  have haa : conj a * a = 1 := by
    rw [mul_comm, mul_conj, normSq_eq_norm_sq, ha]; simp
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  constructor
  · intro h
    have : conj a * b = conj a * a := by rw [haa]; linear_combination -h
    exact (mul_left_cancel₀ (by simpa using ha0) this).symm
  · rintro rfl; rw [haa]; ring

end Problem4

/-! ## Problem 5: `a z + b z̄ + c = 0` -/

section Problem5

theorem conj_mul_self' (a : ℂ) : conj a * a = (normSq a : ℂ) := by rw [mul_comm, mul_conj]

/-- If `|a| ≠ |b|` the unique solution is `z = (b c̄ - ā c) / (|a|² - |b|²)`. -/
theorem problem5_solution (a b c : ℂ) (hab : ‖a‖ ≠ ‖b‖) (z : ℂ) :
    a * z + b * conj z + c = 0 ↔ z = (b * conj c - conj a * c) / (normSq a - normSq b) := by
  have hne : (normSq a - normSq b : ℂ) ≠ 0 := by
    rw [← ofReal_sub, ofReal_ne_zero, sub_ne_zero]
    intro h; apply hab
    rw [← Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _)] at h
    simpa [Complex.norm_def] using h
  rw [eq_div_iff hne]
  constructor
  · intro h
    have h' : conj a * conj z + conj b * z + conj c = 0 := by
      have := congrArg conj h; simpa using this
    have e1 := conj_mul_self' a
    have e2 := conj_mul_self' b
    rw [mul_comm (conj b)] at e2
    linear_combination (conj a) * h - b * h' - z * e1 + z * e2
  · intro h
    -- conversely the formula gives a solution
    have e1 := conj_mul_self' a
    have e2 := conj_mul_self' b
    have hz : z = (b * conj c - conj a * c) / (normSq a - normSq b) := by
      rw [eq_div_iff hne]; exact h
    have hzc : conj z = (conj b * c - a * conj c) / (normSq a - normSq b) := by
      rw [hz, map_div₀]; simp [map_sub, map_mul]
    rw [hzc, hz]
    field_simp
    linear_combination (-c) * e1 + c * e2

/-- If `|a| = |b|`, the equation never has exactly one solution. -/
theorem problem5_not_unique (a b c : ℂ) (hab : ‖a‖ = ‖b‖) :
    ¬ ∃! z, a * z + b * conj z + c = 0 := by
  rintro ⟨z₀, hz₀, huniq⟩
  -- find `u ≠ 0` with `a u + b ū = 0`; then `z₀ + u` is another solution.
  suffices ∃ u : ℂ, u ≠ 0 ∧ a * u + b * conj u = 0 by
    obtain ⟨u, hu, hu'⟩ := this
    have := huniq (z₀ + u) (by
      change a * (z₀ + u) + b * conj (z₀ + u) + c = 0
      rw [map_add]; linear_combination hz₀ + hu')
    exact hu (by linear_combination this)
  by_cases ha : a = 0
  · have hb : b = 0 := by rw [ha, norm_zero] at hab; exact norm_eq_zero.mp hab.symm
    exact ⟨1, one_ne_zero, by simp [ha, hb]⟩
  · -- `u` a square root of `-b / a`, which has modulus one
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) (n := 2) (by norm_num)
    have hnorm : ‖u‖ = 1 := by
      have : ‖u‖ ^ 2 = 1 := by
        rw [← norm_pow, hu, norm_div, norm_neg, hab, div_self]
        rw [← hab]; exact norm_ne_zero_iff.mpr ha
      nlinarith [norm_nonneg u]
    have hu0 : u ≠ 0 := by rintro rfl; simp at hnorm
    have huc : u * conj u = 1 := by
      rw [mul_conj, normSq_eq_norm_sq, hnorm]; simp
    refine ⟨u, hu0, ?_⟩
    have : a * u ^ 2 = -b := by rw [hu]; field_simp
    have hcu : conj u = 1 / u := by rw [eq_div_iff hu0]; rw [mul_comm]; exact huc
    rw [hcu]; field_simp; linear_combination this

/-- Summary: the equation has exactly one solution iff `|a| ≠ |b|`. -/
theorem problem5 (a b c : ℂ) : (∃! z, a * z + b * conj z + c = 0) ↔ ‖a‖ ≠ ‖b‖ := by
  constructor
  · intro h hab; exact problem5_not_unique a b c hab h
  · intro hab
    exact ⟨_, (problem5_solution a b c hab _).mpr rfl,
      fun z hz => (problem5_solution a b c hab z).mp hz⟩

end Problem5

/-! ## Problem 6: Lagrange's identity -/

section Problem6

theorem problem6 (n : ℕ) (a b : ℕ → ℂ) :
    ‖∑ i ∈ range n, a i * b i‖ ^ 2 =
      (∑ i ∈ range n, ‖a i‖ ^ 2) * (∑ i ∈ range n, ‖b i‖ ^ 2) -
        ∑ j ∈ range n, ∑ i ∈ range j, ‖a i * conj (b j) - a j * conj (b i)‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← mul_conj', map_sum, map_mul, map_sub, conj_conj]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ]
    have key : ∑ i ∈ range n,
        (a i * conj (b n) - a n * conj (b i)) * (conj (a i) * b n - conj (a n) * b i) =
        (∑ i ∈ range n, a i * conj (a i)) * (b n * conj (b n)) +
        (a n * conj (a n)) * (∑ i ∈ range n, b i * conj (b i)) -
        (∑ i ∈ range n, a i * b i) * (conj (a n) * conj (b n)) -
        (∑ i ∈ range n, conj (a i) * conj (b i)) * (a n * b n) := by
      simp only [sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => by ring
    linear_combination ih + key

end Problem6

/-! ## Problem 7 -/

theorem problem7 (a b : ℂ) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖(a - b) / (1 - conj a * b)‖ < 1 := by
  have h := normSq_one_sub_conj_mul_sub a b
  have hpos : 0 < (1 - normSq a) * (1 - normSq b) := by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq]
    apply mul_pos <;> nlinarith [norm_nonneg a, norm_nonneg b]
  have hden : 0 < normSq (1 - conj a * b) := by nlinarith [normSq_nonneg (a - b)]
  rw [norm_div, div_lt_one (by rw [norm_pos_iff]; exact normSq_pos.mp hden)]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  linarith

/-! ## Problem 8 -/

theorem problem8 {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ) (ha : ∀ i, ‖a i‖ < 1)
    (hl : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1) :
    ‖∑ i, (lam i : ℂ) * a i‖ < 1 := by
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hsum; norm_num at hsum
  obtain ⟨j, -, hj⟩ : ∃ j ∈ univ, 0 < lam j := by
    by_contra! h
    have : ∑ i, lam i ≤ 0 := sum_nonpos fun i _ => h i (mem_univ i)
    linarith
  calc ‖∑ i, (lam i : ℂ) * a i‖ ≤ ∑ i, ‖(lam i : ℂ) * a i‖ := norm_sum_le _ _
    _ = ∑ i, lam i * ‖a i‖ := by
        refine sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_real, Real.norm_of_nonneg (hl i)]
    _ < ∑ i, lam i := by
        apply sum_lt_sum
        · intro i _; exact mul_le_of_le_one_right (hl i) (ha i).le
        · exact ⟨j, mem_univ j, mul_lt_of_lt_one_right hj (ha j)⟩
    _ = 1 := hsum

/-! ## Problem 9: multiple angle formulas -/

section Problem9


theorem problem9_cos3 (φ : ℝ) : Real.cos (3 * φ) = Real.cos φ ^ 3 - 3 * Real.cos φ * Real.sin φ ^ 2 := by
  rw [show 3 * φ = φ + φ + φ by ring]
  simp only [Real.cos_add, Real.sin_add]; ring

theorem problem9_cos4 (φ : ℝ) :
    Real.cos (4 * φ) = Real.cos φ ^ 4 - 6 * Real.cos φ ^ 2 * Real.sin φ ^ 2 + Real.sin φ ^ 4 := by
  rw [show 4 * φ = φ + φ + φ + φ by ring]
  simp only [Real.cos_add, Real.sin_add]; ring

theorem problem9_sin5 (φ : ℝ) :
    Real.sin (5 * φ) = 5 * Real.cos φ ^ 4 * Real.sin φ - 10 * Real.cos φ ^ 2 * Real.sin φ ^ 3 + Real.sin φ ^ 5 := by
  rw [show 5 * φ = φ + φ + φ + φ + φ by ring]
  simp only [Real.cos_add, Real.sin_add]; ring

end Problem9

/-! ## Problem 10: `∑ Real.cos kx` and `∑ Real.sin kx` -/

section Problem10


theorem problem10_cos_aux (u : ℝ) (n : ℕ) :
    2 * Real.sin u * ∑ k ∈ range (n + 1), Real.cos (k * (2 * u)) = Real.sin ((2 * n + 1) * u) + Real.sin u := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 : (2 * ((n + 1 : ℕ) : ℝ) + 1) * u = (n + 1 : ℕ) * (2 * u) + u := by ring
    have h2 : (2 * (n : ℝ) + 1) * u = (n + 1 : ℕ) * (2 * u) - u := by push_cast; ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

theorem problem10_sin_aux (u : ℝ) (n : ℕ) :
    2 * Real.sin u * ∑ k ∈ range (n + 1), Real.sin (k * (2 * u)) = Real.cos u - Real.cos ((2 * n + 1) * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 : (2 * ((n + 1 : ℕ) : ℝ) + 1) * u = (n + 1 : ℕ) * (2 * u) + u := by ring
    have h2 : (2 * (n : ℝ) + 1) * u = (n + 1 : ℕ) * (2 * u) - u := by push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]; ring

/-- `1 + Real.cos x + ⋯ + Real.cos nx = Real.sin((n+1)x/2) Real.cos(nx/2) / Real.sin(x/2)`. -/
theorem problem10_cos (x : ℝ) (n : ℕ) (hx : Real.sin (x / 2) ≠ 0) :
    ∑ k ∈ range (n + 1), Real.cos (k * x) = Real.sin ((n + 1) * x / 2) * Real.cos (n * x / 2) / Real.sin (x / 2) := by
  rw [eq_div_iff hx]
  have h := problem10_cos_aux (x / 2) n
  rw [show 2 * (x / 2) = x by ring] at h
  have h3 : Real.sin ((2 * n + 1) * (x / 2)) + Real.sin (x / 2) =
      2 * (Real.sin ((n + 1) * x / 2) * Real.cos (n * x / 2)) := by
    rw [show (2 * (n : ℝ) + 1) * (x / 2) = (n + 1) * x / 2 + n * x / 2 by ring,
      show x / 2 = (n + 1) * x / 2 - n * x / 2 by ring, Real.sin_add, Real.sin_sub]
    ring_nf
  linarith

/-- `Real.sin x + ⋯ + Real.sin nx = Real.sin((n+1)x/2) Real.sin(nx/2) / Real.sin(x/2)`. -/
theorem problem10_sin (x : ℝ) (n : ℕ) (hx : Real.sin (x / 2) ≠ 0) :
    ∑ k ∈ range (n + 1), Real.sin (k * x) = Real.sin ((n + 1) * x / 2) * Real.sin (n * x / 2) / Real.sin (x / 2) := by
  rw [eq_div_iff hx]
  have h := problem10_sin_aux (x / 2) n
  rw [show 2 * (x / 2) = x by ring] at h
  have h3 : Real.cos (x / 2) - Real.cos ((2 * n + 1) * (x / 2)) =
      2 * (Real.sin ((n + 1) * x / 2) * Real.sin (n * x / 2)) := by
    rw [show (2 * (n : ℝ) + 1) * (x / 2) = (n + 1) * x / 2 + n * x / 2 by ring,
      show x / 2 = (n + 1) * x / 2 - n * x / 2 by ring, Real.cos_add, Real.cos_sub]
    ring_nf
  linarith

end Problem10

/-! ## Problem 11: sums of roots of unity -/

theorem problem11 (n : ℕ) (hn : n ≠ 0) (h : ℤ) (hh : ¬ (n : ℤ) ∣ h) :
    ∑ k ∈ range n, exp (2 * Real.pi * I / n) ^ (h * k) = 0 := by
  set ω := exp (2 * Real.pi * I / n)
  have hω : IsPrimitiveRoot ω n := isPrimitiveRoot_exp n hn
  have hω0 : ω ≠ 0 := exp_ne_zero _
  set r := ω ^ h
  have hr1 : r ≠ 1 := by rwa [Ne, hω.zpow_eq_one_iff_dvd]
  have hrn : r ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one, one_zpow]
  have : ∀ k : ℕ, ω ^ (h * k) = r ^ k := fun k => by rw [zpow_mul, zpow_natCast]
  simp_rw [this]
  rw [geom_sum_eq hr1, hrn, sub_self, zero_div]

end HW1
