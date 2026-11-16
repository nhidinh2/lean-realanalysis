import Mathlib

/-!
# Homework 3: linear (Möbius) transformations

Formalizations of Homework 3 (Ahlfors, Ch. 3, §3).
-/

open Complex ComplexConjugate Filter Topology

noncomputable section

namespace HW3

/-! ## Problem 1: `|f² - 1| < 1` forces a constant sign of `Re f` -/

theorem problem1 {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsPreconnected Ω) (hf : ContinuousOn f Ω)
    (h : ∀ z ∈ Ω, ‖f z ^ 2 - 1‖ < 1) :
    (∀ z ∈ Ω, 0 < (f z).re) ∨ (∀ z ∈ Ω, (f z).re < 0) := by
  -- `Re f` never vanishes
  have hne : ∀ z ∈ Ω, (f z).re ≠ 0 := by
    intro z hz h0
    have h1 := h z hz
    set v := (f z).im
    have hfz : f z = v * I := by apply Complex.ext <;> simp [h0, v]
    have : f z ^ 2 - 1 = ((-(v ^ 2) - 1 : ℝ) : ℂ) := by
      rw [hfz]; push_cast; ring_nf; rw [I_sq]; ring
    rw [this, norm_real, Real.norm_eq_abs, abs_of_neg (by nlinarith)] at h1
    nlinarith
  have hcont : ContinuousOn (fun z => (f z).re) Ω := continuous_re.comp_continuousOn hf
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hcon
  have ha'' : (f a).re < 0 := lt_of_le_of_ne ha' (hne a ha)
  have hb'' : 0 < (f b).re := lt_of_le_of_ne hb' (hne b hb).symm
  obtain ⟨c, hc, hc0⟩ := hΩ.intermediate_value ha hb hcont ⟨ha''.le, hb''.le⟩
  exact hne c hc hc0

/-! ## Problem 2: reflection `z ↦ z̄` is not a linear transformation -/

theorem problem2 :
    ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      ∀ z : ℂ, c * z + d ≠ 0 → conj z = (a * z + b) / (c * z + d) := by
  rintro ⟨a, b, c, d, hdet, h⟩
  -- the set where the formula holds is dense
  have hdense : Dense {z : ℂ | c * z + d ≠ 0} := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by rintro rfl; simp [hc] at hdet
      have : {z : ℂ | c * z + d ≠ 0} = Set.univ := by ext z; simp [hc, hd]
      rw [this]; exact dense_univ
    · refine (dense_compl_singleton (-d / c)).mono fun z hz => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
      intro h0; apply hz; field_simp; linear_combination h0
  have hext : (fun z => conj z * (c * z + d)) = fun z => a * z + b := by
    refine Continuous.ext_on hdense (by fun_prop) (by fun_prop) fun z hz => ?_
    rw [h z hz, div_mul_cancel₀ _ hz]
  have e : ∀ z, conj z * (c * z + d) = a * z + b := fun z => congrFun hext z
  have e0 := e 0
  have e1 := e 1
  have e2 := e (-1)
  have e3 := e I
  simp only [map_zero, map_one, map_neg, conj_I] at e0 e1 e2 e3
  have hb : b = 0 := by linear_combination -e0
  have hc : c = 0 := by linear_combination (e1 + e2) / 2 + hb
  have hd : d = a := by linear_combination (e1 - e2) / 2
  have ha : a * (2 * I) = 0 := by
    linear_combination -e3 - I ^ 2 * hc - I * hd - hb
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exfalso; simp at h
  apply hdet
  rw [hb, hc, hd, ha0]; ring

/-! ## Problem 3: compositions -/

section Problem3

def T₁ (z : ℂ) : ℂ := (z + 2) / (z + 3)
def T₂ (z : ℂ) : ℂ := z / (z + 1)

theorem problem3_T₁T₂ (z : ℂ) (h1 : z + 1 ≠ 0) (h2 : 4 * z + 3 ≠ 0) :
    T₁ (T₂ z) = (3 * z + 2) / (4 * z + 3) := by
  unfold T₁ T₂
  have : z / (z + 1) + 3 ≠ 0 := by
    rw [div_add' _ _ _ h1]; exact div_ne_zero (fun h => h2 (by linear_combination h)) h1
  field_simp
  ring

theorem problem3_T₂T₁ (z : ℂ) (h1 : z + 3 ≠ 0) (h2 : 2 * z + 5 ≠ 0) :
    T₂ (T₁ z) = (z + 2) / (2 * z + 5) := by
  unfold T₁ T₂
  have : (z + 2) / (z + 3) + 1 ≠ 0 := by
    rw [div_add' _ _ _ h1]; exact div_ne_zero (fun h => h2 (by linear_combination h)) h1
  field_simp
  ring

/-- `T₁⁻¹ T₂ z = z - 2`, i.e. `T₁ (z - 2) = T₂ z`. -/
theorem problem3_T₁invT₂ (z : ℂ) (h1 : z + 1 ≠ 0) : T₁ (z - 2) = T₂ z := by
  unfold T₁ T₂
  congr 1 <;> ring

end Problem3

/-! ## Problem 4: isometries fixing the origin -/

theorem problem4 (T : ℂ → ℂ) (hT : ∀ z w, ‖T z - T w‖ = ‖z - w‖) (h0 : T 0 = 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ((∀ z, T z = a * z) ∨ (∀ z, T z = a * conj z)) := by
  have hsq : ∀ z w, normSq (T z - T w) = normSq (z - w) := fun z w => by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, hT]
  set a := T 1
  set b := T I
  have na : a.re ^ 2 + a.im ^ 2 = 1 := by
    have := hsq 1 0; rw [h0] at this; simp [normSq_apply] at this; nlinarith [this]
  have nb : b.re ^ 2 + b.im ^ 2 = 1 := by
    have := hsq I 0; rw [h0] at this; simp [normSq_apply] at this; nlinarith [this]
  have Eab : (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 = 2 := by
    have := hsq 1 I; simp [normSq_apply] at this; nlinarith [this]
  have hAB : a.re * b.re + a.im * b.im = 0 := by linear_combination (na + nb - Eab) / 2
  set k := a.re * b.im - a.im * b.re
  have hk : k ^ 2 = 1 := by
    linear_combination (b.re ^ 2 + b.im ^ 2) * na + nb - (a.re * b.re + a.im * b.im) * hAB
  have hb1 : b.re = -a.im * k := by linear_combination a.re * hAB - b.re * na
  have hb2 : b.im = a.re * k := by linear_combination a.im * hAB - b.im * na
  -- the coordinates of `T z`
  have key : ∀ z : ℂ, (T z).re * a.re + (T z).im * a.im = z.re ∧
      (T z).re * b.re + (T z).im * b.im = z.im := by
    intro z
    have E0 := hsq z 0
    have Ea := hsq z 1
    have Eb := hsq z I
    rw [h0] at E0
    simp only [normSq_apply, sub_re, sub_im, sub_zero, one_re, one_im, I_re, I_im] at E0 Ea Eb
    constructor
    · linear_combination (E0 - Ea + na) / 2
    · linear_combination (E0 - Eb + nb) / 2
  have hnorm : ‖a‖ = 1 := by
    have h2 : ‖a‖ ^ 2 = 1 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; linear_combination na
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).mp h2
  have hk' : (k - 1) * (k + 1) = 0 := by linear_combination hk
  refine ⟨a, hnorm, ?_⟩
  rcases mul_eq_zero.mp hk' with h | h
  · left
    intro z
    obtain ⟨hA, hB⟩ := key z
    have h1 : k = 1 := by linear_combination h
    rw [hb1, hb2, h1] at hB
    apply Complex.ext <;> simp only [mul_re, mul_im]
    · linear_combination a.re * hA - a.im * hB - (T z).re * na
    · linear_combination a.im * hA + a.re * hB - (T z).im * na
  · right
    intro z
    obtain ⟨hA, hB⟩ := key z
    have h1 : k = -1 := by linear_combination h
    rw [hb1, hb2, h1] at hB
    apply Complex.ext <;> simp only [mul_re, mul_im, conj_re, conj_im]
    · linear_combination a.re * hA + a.im * hB - (T z).re * na
    · linear_combination a.im * hA - a.re * hB - (T z).im * na

/-! ## Problem 5: linear transformations preserving the real axis -/

theorem problem5 (a b c d : ℂ) (hdet : a * d - b * c ≠ 0)
    (hreal : ∀ x : ℝ, c * x + d ≠ 0 → ((a * x + b) / (c * x + d)).im = 0) :
    ∃ t : ℂ, t ≠ 0 ∧ (t * a).im = 0 ∧ (t * b).im = 0 ∧ (t * c).im = 0 ∧ (t * d).im = 0 := by
  -- Step 1: `Im((a x + b) conj(c x + d)) = 0` for all real `x`.
  set A := (a * conj c).im
  set B := (a * conj d + b * conj c).im
  set C := (b * conj d).im
  have hpoly : ∀ x : ℝ, ((a * x + b) * conj (c * x + d)).im = A * x ^ 2 + B * x + C := by
    intro x
    simp only [A, B, C, map_add, map_mul, conj_ofReal, mul_im, add_im, mul_re, add_re, ofReal_re,
      ofReal_im, conj_re, conj_im]
    ring
  have hgood : ∀ x : ℝ, c * x + d ≠ 0 → A * x ^ 2 + B * x + C = 0 := by
    intro x hx
    rw [← hpoly]
    set q := (a * x + b) / (c * x + d)
    have hq : a * x + b = q * (c * x + d) := by rw [div_mul_cancel₀ _ hx]
    rw [hq, mul_assoc, mul_conj, mul_im, ofReal_re, ofReal_im, hreal x hx]
    ring
  have hdense : Dense {x : ℝ | c * x + d ≠ 0} := by
    refine (dense_compl_singleton (-d / c).re).mono fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    intro h0; apply hx
    have hc : c ≠ 0 := by rintro rfl; simp at h0; subst h0; simp at hdet
    have : (x : ℂ) = -d / c := by field_simp; linear_combination h0
    rw [← this, ofReal_re]
  have hall : ∀ x : ℝ, A * x ^ 2 + B * x + C = 0 := by
    have := Continuous.ext_on hdense (f := fun x : ℝ => A * x ^ 2 + B * x + C) (g := fun _ => 0)
      (by fun_prop) (by fun_prop) (fun x hx => hgood x hx)
    exact fun x => congrFun this x
  have hC : C = 0 := by simpa using hall 0
  have hA : A = 0 := by have h1 := hall 1; have h2 := hall (-1); linarith
  have hB : B = 0 := by have h1 := hall 1; simp [hA, hC] at h1; linarith
  -- Step 2: choose the scalar
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by rintro rfl; simp [hc] at hdet
    refine ⟨conj d, by simpa using hd, ?_, ?_, by simp [hc], ?_⟩
    · have : (conj d * a).im = (a * conj d + b * conj c).im := by rw [hc]; simp; ring
      rw [this]; exact hB
    · rw [mul_comm]; exact hC
    · rw [mul_comm, mul_conj]; simp
  · have hR : 0 < c.re ^ 2 + c.im ^ 2 := by
      have := normSq_pos.mpr hc; rwa [normSq_apply, ← sq, ← sq] at this
    have hA' : c.re * a.im - c.im * a.re = 0 := by
      have := hA; simp only [A, mul_im, conj_re, conj_im] at this; linarith
    have hB' : a.im * d.re - a.re * d.im + b.im * c.re - b.re * c.im = 0 := by
      have := hB; simp only [B, add_im, mul_im, conj_re, conj_im] at this; linarith
    have hC' : b.im * d.re - b.re * d.im = 0 := by
      have := hC; simp only [C, mul_im, conj_re, conj_im] at this; linarith
    set D := (conj c * a) * (conj c * d) - (conj c * b) * (conj c * c) with hDdef
    have hD : D ≠ 0 := by
      have : D = conj c ^ 2 * (a * d - b * c) := by rw [hDdef]; ring
      rw [this]; exact mul_ne_zero (pow_ne_zero _ (by simpa using hc)) hdet
    have hDim : D.im = 0 := by
      simp only [D, sub_im, mul_im, mul_re, conj_re, conj_im]
      linear_combination (-(c.re ^ 2 + c.im ^ 2)) * hB' + 2 * (c.re * d.re + c.im * d.im) * hA'
    have hDre : D.re * (c.re * d.im - c.im * d.re) = 0 := by
      simp only [D, sub_re, mul_im, mul_re, conj_re, conj_im]
      linear_combination (c.re ^ 2 + c.im ^ 2) ^ 2 * hC' -
        (c.re ^ 2 + c.im ^ 2) * (c.re * d.re + c.im * d.im) * hB' +
        ((c.re * d.re + c.im * d.im) ^ 2 - (c.re * d.im - c.im * d.re) ^ 2) * hA'
    have hDre0 : D.re ≠ 0 := fun h => hD (Complex.ext (by simp [h]) (by simp [hDim]))
    have hSim : c.re * d.im - c.im * d.re = 0 := (mul_eq_zero.mp hDre).resolve_left hDre0
    have hQim : (c.re ^ 2 + c.im ^ 2) * (c.re * b.im - c.im * b.re) = 0 := by
      linear_combination (c.re * a.re + c.im * a.im) * hSim + (c.re ^ 2 + c.im ^ 2) * hB' -
        (c.re * d.re + c.im * d.im) * hA'
    have hQim' : c.re * b.im - c.im * b.re = 0 := (mul_eq_zero.mp hQim).resolve_left hR.ne'
    refine ⟨conj c, by simpa using hc, ?_, ?_, by rw [mul_comm, mul_conj]; simp, ?_⟩
    · simp only [mul_im, conj_re, conj_im]; linarith
    · simp only [mul_im, conj_re, conj_im]; linarith
    · simp only [mul_im, conj_re, conj_im]; linarith

/-! ## Problem 6 -/

def T6 (z : ℂ) : ℂ := (z + I) / (I - 3 * z)

theorem problem6 : T6 0 = 1 ∧ T6 I = -1 ∧ T6 (-I) = 0 := by
  have hI : I - 3 * I ≠ 0 := by
    rw [show I - 3 * I = -2 * I by ring]; simp
  refine ⟨by simp [T6], ?_, by simp [T6]⟩
  unfold T6
  rw [div_eq_iff hI]; ring

/-! ## Problem 7: the six cross ratios -/

section Problem7

/-- The cross ratio `(z₁, z₂, z₃, z₄)`. -/
def cr (z₁ z₂ z₃ z₄ : ℂ) : ℂ := (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃))

variable {z₁ z₂ z₃ z₄ : ℂ}

/-- Invariance under the Klein four-group of double transpositions. -/
theorem cr_klein :
    cr z₂ z₁ z₄ z₃ = cr z₁ z₂ z₃ z₄ ∧ cr z₃ z₄ z₁ z₂ = cr z₁ z₂ z₃ z₄ ∧
      cr z₄ z₃ z₂ z₁ = cr z₁ z₂ z₃ z₄ := by
  unfold cr
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> ring

theorem cr_swap34 : cr z₁ z₂ z₄ z₃ = (cr z₁ z₂ z₃ z₄)⁻¹ := by
  unfold cr; rw [inv_div]

theorem one_sub_cr (h14 : z₁ ≠ z₄) (h23 : z₂ ≠ z₃) :
    1 - cr z₁ z₂ z₃ z₄ = cr z₁ z₃ z₂ z₄ := by
  have h14' : z₁ - z₄ ≠ 0 := sub_ne_zero.mpr h14
  have h23' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
  have h32' : z₃ - z₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  unfold cr; field_simp; ring

/-- With `λ = (z₁, z₂, z₃, z₄)` and distinct points, the 24 permutations give the six values
`λ, 1/λ, 1 - λ, 1/(1 - λ), λ/(λ - 1), (λ - 1)/λ`. -/
theorem problem7 (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h14 : z₁ ≠ z₄) (h23 : z₂ ≠ z₃)
    (h24 : z₂ ≠ z₄) (h34 : z₃ ≠ z₄) :
    let l := cr z₁ z₂ z₃ z₄
    cr z₁ z₂ z₄ z₃ = 1 / l ∧
    cr z₁ z₃ z₂ z₄ = 1 - l ∧
    cr z₁ z₃ z₄ z₂ = 1 / (1 - l) ∧
    cr z₁ z₄ z₃ z₂ = l / (l - 1) ∧
    cr z₁ z₄ z₂ z₃ = (l - 1) / l := by
  intro l
  have hl : l ≠ 0 := by
    simp only [l, cr]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h13) (sub_ne_zero.mpr h24))
      (mul_ne_zero (sub_ne_zero.mpr h14) (sub_ne_zero.mpr h23))
  have h1l : 1 - l ≠ 0 := by
    rw [one_sub_cr h14 h23]; unfold cr
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h34))
      (mul_ne_zero (sub_ne_zero.mpr h14) (sub_ne_zero.mpr h23.symm))
  have hl1 : l - 1 ≠ 0 := fun h => h1l (by linear_combination -h)
  have e1 : cr z₁ z₂ z₄ z₃ = 1 / l := by rw [cr_swap34, one_div]
  have e2 : cr z₁ z₃ z₂ z₄ = 1 - l := (one_sub_cr h14 h23).symm
  have e3 : cr z₁ z₃ z₄ z₂ = 1 / (1 - l) := by rw [cr_swap34, e2, one_div]
  have e4 : cr z₁ z₄ z₃ z₂ = l / (l - 1) := by
    rw [← one_sub_cr (z₂ := z₃) (z₃ := z₄) h12 h34, e3]; field_simp; ring
  have e5 : cr z₁ z₄ z₂ z₃ = (l - 1) / l := by
    rw [cr_swap34, e4, inv_div]
  exact ⟨e1, e2, e3, e4, e5⟩

end Problem7

/-! ## Problem 8: carrying four points to `1, -1, k, -k` -/

section Problem8

theorem problem8_cr (k : ℂ) (hk1 : k ≠ 1) (hk2 : k ≠ -1) (hk0 : k ≠ 0) :
    cr 1 (-1) k (-k) = (1 - k) ^ 2 / (1 + k) ^ 2 := by
  have h1 : 1 + k ≠ 0 := fun h => hk2 (by linear_combination h)
  have h2 : -1 - k ≠ 0 := fun h => hk2 (by linear_combination -h)
  unfold cr
  rw [show (1 : ℂ) - -k = 1 + k by ring, show (-1 : ℂ) - k = -(1 + k) by ring,
    show (-1 : ℂ) - -k = -(1 - k) by ring]
  field_simp
  try ring

/-- `(1, -1, k, -k) = λ` is the quadratic `(λ - 1)k² + 2(λ + 1)k + (λ - 1) = 0`. -/
theorem problem8_quadratic (l k : ℂ) (hk : 1 + k ≠ 0) :
    (1 - k) ^ 2 / (1 + k) ^ 2 = l ↔ (l - 1) * k ^ 2 + 2 * (l + 1) * k + (l - 1) = 0 := by
  rw [div_eq_iff (pow_ne_zero 2 hk)]
  constructor <;> intro h <;> linear_combination -h

/-- For `λ ≠ 0, 1` the quadratic has exactly two roots, `k` and `1/k`, and neither is `0, ±1`. -/
theorem problem8_roots (l : ℂ) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ∃ k : ℂ, k ≠ 1 / k ∧ k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧
      ∀ w : ℂ, (l - 1) * w ^ 2 + 2 * (l + 1) * w + (l - 1) = 0 ↔ w = k ∨ w = 1 / k := by
  have hA : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim (l - 1) (2 * (l + 1)) (l - 1))
  have hdisc : discrim (l - 1) (2 * (l + 1)) (l - 1) = 16 * l := by unfold discrim; ring
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [hdisc] at hs; simp at hs; exact hl0 hs
  set k := (-(2 * (l + 1)) + s) / (2 * (l - 1))
  set k' := (-(2 * (l + 1)) - s) / (2 * (l - 1))
  have hroots : ∀ w : ℂ, (l - 1) * w ^ 2 + 2 * (l + 1) * w + (l - 1) = 0 ↔ w = k ∨ w = k' := by
    intro w
    rw [← quadratic_eq_zero_iff hA hs w]; ring_nf
  have hprod : k * k' = 1 := by
    simp only [k, k']
    field_simp
    have : s * s = 16 * l := by rw [← hs, hdisc]
    linear_combination -this
  have hk0 : k ≠ 0 := by rintro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have hk' : k' = 1 / k := by rw [eq_div_iff hk0]; linear_combination hprod
  have hkk' : k ≠ k' := by
    intro h
    simp only [k, k'] at h
    rw [div_left_inj' (mul_ne_zero two_ne_zero hA)] at h
    exact hs0 (by linear_combination h / 2)
  have hroot_k : (l - 1) * k ^ 2 + 2 * (l + 1) * k + (l - 1) = 0 := (hroots k).mpr (Or.inl rfl)
  refine ⟨k, hk' ▸ hkk', hk0, ?_, ?_, ?_⟩
  · rintro h; rw [h] at hroot_k; exact hl0 (by linear_combination hroot_k / 4)
  · rintro h; rw [h] at hroot_k
    have : (-4 : ℂ) = 0 := by linear_combination hroot_k
    norm_num at this
  · intro w; rw [hroots, hk']

end Problem8

/-! ## Problem 9: reflections in the circle `|z - 2| = 1` -/

section Problem9

/-- Reflection in the circle `|z - 2| = 1`. -/
def refl (z : ℂ) : ℂ := 2 + 1 / conj (z - 2)

theorem refl_re_im (x y : ℝ) :
    (refl ⟨x, y⟩).re = 2 + (x - 2) / ((x - 2) ^ 2 + y ^ 2) ∧
    (refl ⟨x, y⟩).im = y / ((x - 2) ^ 2 + y ^ 2) := by
  unfold refl
  constructor <;> simp [Complex.div_re, Complex.div_im, normSq_apply] <;> ring

theorem norm_eq_of_normSq {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : normSq w = r ^ 2) : ‖w‖ = r := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hr, ← normSq_eq_norm_sq, h]

/-- The imaginary axis is reflected into `|w - 7/4| = 1/4`. -/
theorem problem9_imag_axis (y : ℝ) : ‖refl ⟨0, y⟩ - 7 / 4‖ = 1 / 4 := by
  apply norm_eq_of_normSq (by norm_num)
  obtain ⟨h1, h2⟩ := refl_re_im 0 y
  have hD : (0 - 2) ^ 2 + y ^ 2 ≠ 0 := by positivity
  rw [normSq_apply, sub_re, sub_im, h1, h2]
  norm_num
  field_simp
  ring

/-- The line `x = y` is reflected into `|w - (7/4 + i/4)| = √2/4`. -/
theorem problem9_diagonal (x : ℝ) :
    ‖refl ⟨x, x⟩ - (7 / 4 + I / 4)‖ = Real.sqrt 2 / 4 := by
  apply norm_eq_of_normSq (by positivity)
  obtain ⟨h1, h2⟩ := refl_re_im x x
  have hD : (x - 2) ^ 2 + x ^ 2 ≠ 0 := by
    intro h; nlinarith [sq_nonneg (x - 2), sq_nonneg x]
  rw [normSq_apply, sub_re, sub_im, h1, h2, div_pow, Real.sq_sqrt (by norm_num)]
  simp
  field_simp
  ring

/-- The unit circle is reflected into `|w - 4/3| = 1/3`. -/
theorem problem9_unit_circle (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    ‖refl ⟨x, y⟩ - 4 / 3‖ = 1 / 3 := by
  apply norm_eq_of_normSq (by norm_num)
  obtain ⟨h1, h2⟩ := refl_re_im x y
  have hx : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hy2 : y ^ 2 = 1 - x ^ 2 := by linarith
  have hD : (x - 2) ^ 2 + y ^ 2 = 5 - 4 * x := by rw [hy2]; ring
  have hD0 : (5 - 4 * x) ≠ 0 := by intro h0; linarith
  rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; ring, normSq_apply, sub_re, sub_im,
    ofReal_re, ofReal_im, h1, h2, hD, sub_zero]
  have hA : 2 + (x - 2) / (5 - 4 * x) - 4 / 3 = (4 - 5 * x) / (3 * (5 - 4 * x)) := by
    rw [eq_div_iff (mul_ne_zero three_ne_zero hD0)]
    have : (x - 2) / (5 - 4 * x) * (5 - 4 * x) = x - 2 := div_mul_cancel₀ _ hD0
    linear_combination 3 * this
  rw [hA, div_mul_div_comm, div_mul_div_comm, ← sq y, hy2]
  field_simp
  ring

end Problem9

/-! ## Problem 10 -/

section Problem10

def T10 (z : ℂ) : ℂ := (z + 2) / (-(1 + I) * z - 2 * I)

theorem problem10 : T10 (-2) = 0 ∧ T10 0 = I ∧
    ∀ z : ℂ, ‖z‖ = 2 → ‖T10 z + 1‖ = 1 := by
  refine ⟨by simp [T10], ?_, ?_⟩
  · unfold T10
    rw [div_eq_iff (by simp)]; ring_nf; rw [I_sq]; ring
  · intro z hz
    have hz2 : z.re ^ 2 + z.im ^ 2 = 4 := by
      have := congrArg (· ^ 2) hz; simp only at this
      rw [← normSq_eq_norm_sq, normSq_apply] at this; nlinarith [this]
    set den := -(1 + I) * z - 2 * I
    have hden_sq : normSq den = 12 + 4 * z.re + 4 * z.im := by
      simp only [den, normSq_apply, sub_re, sub_im, mul_re, mul_im, neg_re, neg_im, add_re,
        add_im, one_re, one_im, I_re, I_im, re_ofNat, im_ofNat]
      linear_combination 2 * hz2
    have hnum_sq : normSq (z + 2 + den) = 12 + 4 * z.re + 4 * z.im := by
      simp only [den, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, neg_re,
        neg_im, one_re, one_im, I_re, I_im, re_ofNat, im_ofNat]
      linear_combination hz2
    have hden : den ≠ 0 := by
      intro h0
      have : normSq den = 0 := by rw [h0, map_zero]
      rw [hden_sq] at this
      -- then `z = -2 - 2i`, contradicting `|z| = 2`
      nlinarith [sq_nonneg (z.re - z.im)]
    have : T10 z + 1 = (z + 2 + den) / den := by
      rw [eq_div_iff hden, add_mul, one_mul]; unfold T10; rw [div_mul_cancel₀ _ hden]
    apply norm_eq_of_normSq (by norm_num)
    rw [this, normSq_div, hnum_sq, ← hden_sq, div_self]
    · norm_num
    · rwa [Ne, map_eq_zero]

end Problem10

/-! ## Problem 11: concentric circles -/

/-- A linear transformation carrying a pair of concentric circles `|z| = r₁, |z| = r₂` onto a pair
of concentric circles `|w - w₀| = ρ₁, ρ₂` preserves the ratio of the radii (larger to smaller). -/
theorem problem11 (a b c d w₀ : ℂ) (hdet : a * d - b * c ≠ 0) (r₁ r₂ ρ₁ ρ₂ : ℝ)
    (hr : 0 < r₁ ∧ r₁ < r₂) (hρ : 0 < ρ₁ ∧ 0 < ρ₂)
    (h₁ : ∀ z : ℂ, ‖z‖ = r₁ → c * z + d ≠ 0 ∧ ‖(a * z + b) / (c * z + d) - w₀‖ = ρ₁)
    (h₂ : ∀ z : ℂ, ‖z‖ = r₂ → c * z + d ≠ 0 ∧ ‖(a * z + b) / (c * z + d) - w₀‖ = ρ₂) :
    ρ₂ / ρ₁ = r₂ / r₁ ∨ ρ₁ / ρ₂ = r₂ / r₁ := by
  sorry

/-! ## Problem 12 -/

section Problem12

/-- `T z = (z - (2 - √3)) / (z - (2 + √3))` carries `|z| = 1` and `|z - 1/4| = 1/4` onto the
concentric circles `|w| = 2 - √3` and `|w| = (2 - √3)²`; the ratio of radii is `2 + √3`. -/
def T12 (z : ℂ) : ℂ := (z - (2 - Real.sqrt 3)) / (z - (2 + Real.sqrt 3))

theorem problem12_1 (z : ℂ) (hz : ‖z‖ = 1) : ‖T12 z‖ = 2 - Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) hz; simp only at this
    rw [← normSq_eq_norm_sq, normSq_apply] at this; nlinarith [this]
  have hx : z.re ≤ 1 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1)]
  have hq : z - (2 + Real.sqrt 3) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  apply norm_eq_of_normSq (by linarith)
  unfold T12
  rw [normSq_div, div_eq_iff (by rwa [Ne, map_eq_zero])]
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
  simp only [sub_zero, add_re, add_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im, add_zero]
  nlinarith [h3, hz2]

theorem problem12_2 (z : ℂ) (hz : ‖z - 1 / 4‖ = 1 / 4) : ‖T12 z‖ = (2 - Real.sqrt 3) ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hz2 : z.re ^ 2 + z.im ^ 2 = z.re / 2 := by
    have := congrArg (· ^ 2) hz; simp only at this
    rw [← normSq_eq_norm_sq, normSq_apply] at this; simp at this; nlinarith [this]
  have hx : z.re ≤ 1 / 2 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1 / 2)]
  have hq : z - (2 + Real.sqrt 3) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  apply norm_eq_of_normSq (by positivity)
  unfold T12
  rw [normSq_div, div_eq_iff (by rwa [Ne, map_eq_zero])]
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
  simp only [sub_zero, add_re, add_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im, add_zero]
  have h34 : Real.sqrt 3 ^ 4 = 9 := by rw [show 4 = 2 * 2 by rfl, pow_mul, h3]; norm_num
  nlinarith [h3, hz2, h34]

theorem problem12_ratio : (2 - Real.sqrt 3) / (2 - Real.sqrt 3) ^ 2 = 2 + Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hne : 2 - Real.sqrt 3 ≠ 0 := by
    intro h; nlinarith
  field_simp
  nlinarith [h3]

end Problem12

end HW3
