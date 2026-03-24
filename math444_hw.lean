import Mathlib

open Set Metric Filter Topology Finset

-- ============================================================================
-- Problem 1 (§1.2 #2)
-- For each n ∈ ℕ, 1³ + 2³ + ⋯ + n³ = (n(n+1)/2)².
-- ============================================================================

section Problem1

theorem problem1 (n : ℕ) :
    4 * (∑ k ∈ Finset.range n, (k + 1) ^ 3) = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    ring_nf
    ring_nf at ih
    omega

end Problem1

-- ============================================================================
-- Problem 2 (§1.3 #6)
-- There exists a bijection between ℕ and a proper subset of itself.
-- ============================================================================

section Problem2

/-- The even naturals are a proper subset of ℕ, and n ↦ 2n is a bijection. -/
theorem problem2 : ∃ (S : Set ℕ) (_ : S ≠ Set.univ),
    S ⊆ Set.univ ∧ ∃ f : ℕ → S, Function.Bijective f := by
  refine ⟨{n | ∃ k, n = 2 * k}, ?_, Set.subset_univ _, ?_⟩
  · intro h
    have : 1 ∈ (Set.univ : Set ℕ) := Set.mem_univ 1
    rw [← h] at this
    simp [Set.mem_setOf_eq] at this
    omega
  · refine ⟨fun n => ⟨2 * n, ⟨n, rfl⟩⟩, ?_, ?_⟩
    · intro a b h
      simp [Subtype.mk.injEq] at h
      omega
    · rintro ⟨y, k, rfl⟩
      exact ⟨k, by simp⟩

end Problem2

-- ============================================================================
-- Problem 3 (§2.1 #4)
-- If a ∈ ℝ satisfies a · a = a, then a = 0 or a = 1.
-- ============================================================================

section Problem3

theorem problem3 (a : ℝ) (h : a * a = a) : a = 0 ∨ a = 1 := by
  have h' : a * (a - 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h' with ha | ha
  · left; exact ha
  · right; linarith

end Problem3

-- ============================================================================
-- Problem 4 (§2.2 #5)
-- If a < x < b and a < y < b, then |x - y| < b - a.
-- ============================================================================

section Problem4

theorem problem4 (a b x y : ℝ)
    (hx : a < x ∧ x < b) (hy : a < y ∧ y < b) :
    |x - y| < b - a := by
  rw [abs_lt]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

end Problem4

-- ============================================================================
-- Problem 5 (§2.1 #9)
-- Q(√2) = { s + t√2 : s, t ∈ ℚ } is closed under +, −, and reciprocal.
-- ============================================================================

section Problem5

def QSqrt2 : Set ℝ := { x | ∃ s t : ℚ, x = (s : ℝ) + (t : ℝ) * Real.sqrt 2 }

theorem problem5_add (x : ℝ) (hx : x ∈ QSqrt2) (y : ℝ) (hy : y ∈ QSqrt2) :
    x + y ∈ QSqrt2 := by
  obtain ⟨s₁, t₁, rfl⟩ := hx
  obtain ⟨s₂, t₂, rfl⟩ := hy
  exact ⟨s₁ + s₂, t₁ + t₂, by push_cast; ring⟩

theorem problem5_sub (x : ℝ) (hx : x ∈ QSqrt2) (y : ℝ) (hy : y ∈ QSqrt2) :
    x - y ∈ QSqrt2 := by
  obtain ⟨s₁, t₁, rfl⟩ := hx
  obtain ⟨s₂, t₂, rfl⟩ := hy
  exact ⟨s₁ - s₂, t₁ - t₂, by push_cast; ring⟩

theorem problem5_inv (x : ℝ) (hx : x ∈ QSqrt2) (hne : x ≠ 0) :
    x⁻¹ ∈ QSqrt2 := by
  sorry

end Problem5

-- ============================================================================
-- Problem 6 (§2.2 #4)
-- |x - a| < ε ↔ a - ε < x < a + ε.
-- ============================================================================

section Problem6

theorem problem6 (x a ε : ℝ) (hε : ε > 0) :
    |x - a| < ε ↔ a - ε < x ∧ x < a + ε := by
  rw [abs_lt]
  constructor
  · intro ⟨h1, h2⟩; constructor <;> linarith
  · intro ⟨h1, h2⟩; constructor <;> linarith

end Problem6

-- ============================================================================
-- Problem 7 (§2.3 #6)
-- If S ⊂ ℝ is nonempty and bounded below, then inf S = −sup(−S).
-- ============================================================================

section Problem7

theorem problem7 (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S) :
    sInf S = -sSup {x | -x ∈ S} := by
  simp only [Real.sInf_eq_neg_sSup_neg S]

end Problem7

-- ============================================================================
-- Problem 8 (§2.4 #11)
-- sup_y inf_x h(x,y) ≤ inf_x sup_y h(x,y) (minimax inequality).
-- ============================================================================

section Problem8

theorem problem8 {X Y : Type*} (h : X → Y → ℝ)
    [Nonempty X] [Nonempty Y]
    (hbdd_above : ∀ x, BddAbove (Set.range (fun y => h x y)))
    (hbdd_below : ∀ y, BddBelow (Set.range (fun x => h x y)))
    (hbdd_f : BddBelow (Set.range (fun x => sSup (Set.range (fun y => h x y)))))
    (hbdd_g : BddAbove (Set.range (fun y => sInf (Set.range (fun x => h x y))))) :
    sSup (Set.range (fun y => sInf (Set.range (fun x => h x y)))) ≤
    sInf (Set.range (fun x => sSup (Set.range (fun y => h x y)))) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y, rfl⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  apply le_trans (csInf_le (hbdd_below y) (Set.mem_range_self x))
  apply le_csSup (hbdd_above x) (Set.mem_range_self y)

end Problem8

-- ============================================================================
-- Problem 9 (§3.1 #10)
-- If xₙ → x and x > 0, then ∃ M, ∀ n ≥ M, xₙ > 0.
-- ============================================================================

section Problem9

theorem problem9 {x : ℕ → ℝ} {l : ℝ}
    (hlim : Filter.Tendsto x Filter.atTop (nhds l))
    (hl : l > 0) :
    ∃ M : ℕ, ∀ n ≥ M, x n > 0 := by
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (l / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.dist_eq] at this
  have := abs_lt.mp this
  linarith

end Problem9

-- ============================================================================
-- Problem 10 (§3.2 #2)
-- Example: two divergent sequences whose sum and product both converge.
-- ============================================================================

section Problem10

/-- xₙ = (-1)ⁿ diverges, yₙ = -(-1)ⁿ diverges,
    but xₙ + yₙ = 0 → 0 and xₙ · yₙ = -1 → -1. -/
theorem problem10 :
    ∃ (x y : ℕ → ℝ),
      ¬ (∃ lx, Filter.Tendsto x Filter.atTop (nhds lx)) ∧
      ¬ (∃ ly, Filter.Tendsto y Filter.atTop (nhds ly)) ∧
      Filter.Tendsto (x + y) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (x * y) Filter.atTop (nhds (-1)) := by
  sorry

end Problem10

-- ============================================================================
-- Problem 11 (§3.3 #9)
-- If A is infinite, bounded above, u = sup A, then ∃ increasing (xₙ) in A
-- with xₙ → u.
-- ============================================================================

section Problem11

theorem problem11 (A : Set ℝ) (hA : A.Infinite) (hbdd : BddAbove A) :
    ∃ x : ℕ → ℝ, (∀ n, x n ∈ A) ∧ StrictMono x ∧
      Filter.Tendsto x Filter.atTop (nhds (sSup A)) := by
  sorry

end Problem11

-- ============================================================================
-- Problem 12 (§3.4 #10)
-- Bounded sequence has a subsequence converging to lim sup.
-- ============================================================================

section Problem12

theorem problem12 {x : ℕ → ℝ}
    (hbdd_above : BddAbove (Set.range x))
    (hbdd_below : BddBelow (Set.range x)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (x ∘ φ) Filter.atTop
        (nhds (limsup x atTop)) := by
  sorry

end Problem12

-- ============================================================================
-- Problem 13 (§3.4 #9)
-- If every subsequence of (xₙ) has a further subsequence converging to 0,
-- then xₙ → 0.
-- ============================================================================

section Problem13

theorem problem13 {x : ℕ → ℝ}
    (h : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        Filter.Tendsto (x ∘ φ ∘ ψ) Filter.atTop (nhds 0)) :
    Filter.Tendsto x Filter.atTop (nhds 0) := by
  by_contra hlim
  rw [Metric.tendsto_atTop] at hlim
  push_neg at hlim
  obtain ⟨ε, hε, hN⟩ := hlim
  -- Build a subsequence with |x(φ n)| ≥ ε via dependent choice
  have : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ε ≤ dist (x (φ n)) 0 := by
    sorry
  obtain ⟨φ, hφmono, hφε⟩ := this
  obtain ⟨ψ, hψmono, hψlim⟩ := h φ hφmono
  rw [Metric.tendsto_atTop] at hψlim
  obtain ⟨M, hM⟩ := hψlim ε hε
  have h1 := hM M le_rfl
  have h2 := hφε (ψ M)
  -- h1 : dist (x ∘ φ ∘ ψ) M 0 < ε, h2 : ε ≤ dist (x (φ (ψ M))) 0
  simp only [Function.comp] at h1
  exact absurd h1 (not_lt.mpr h2)

end Problem13

-- ============================================================================
-- Problem 14 (§3.5 #7)
-- A Cauchy sequence of integers is eventually constant.
-- ============================================================================

section Problem14

theorem problem14 {x : ℕ → ℤ} (hC : CauchySeq (fun n => (x n : ℝ))) :
    ∃ N : ℕ, ∀ m n, m ≥ N → n ≥ N → x m = x n := by
  rw [Metric.cauchySeq_iff] at hC
  obtain ⟨N, hN⟩ := hC (1 / 2) (by norm_num)
  refine ⟨N, fun m n hm hn => ?_⟩
  have h := hN m hm n hn
  rw [Real.dist_eq] at h
  have habs : |(↑(x m) - ↑(x n) : ℝ)| < 1 / 2 := h
  have hcast : (↑(x m) - ↑(x n) : ℝ) = ↑((x m : ℤ) - (x n : ℤ)) := by push_cast; ring
  rw [hcast] at habs
  have : ((x m : ℤ) - (x n : ℤ) : ℤ) = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(↑((x m : ℤ) - (x n : ℤ)) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hne)
    linarith
  omega

end Problem14

-- ============================================================================
-- Problem 15 (§3.5 #8)
-- A bounded, monotone increasing sequence is Cauchy.
-- ============================================================================

section Problem15

theorem problem15 {x : ℕ → ℝ} (hmono : Monotone x) (hbdd : BddAbove (Set.range x)) :
    CauchySeq x := by
  exact (tendsto_atTop_ciSup hmono hbdd).cauchySeq

end Problem15

-- ============================================================================
-- Problem 16 (§3.7 #5)
-- If ∑xₙ converges and ∑yₙ diverges, then ∑(xₙ+yₙ) diverges.
-- ============================================================================

section Problem16

theorem problem16 {x y : ℕ → ℝ}
    (hx : Summable x) (hy : ¬ Summable y) :
    ¬ Summable (x + y) := by
  intro hxy
  have : Summable y := by
    have : y = (x + y) - x := by ext n; simp [Pi.add_apply, add_sub_cancel_left]
    rw [this]
    exact hxy.sub hx
  exact hy this

end Problem16

-- ============================================================================
-- Problem 17 (§3.4 #19)
-- lim sup (xₙ + yₙ) ≤ lim sup xₙ + lim sup yₙ.
-- ============================================================================

section Problem17

theorem problem17 {x y : ℕ → ℝ}
    (hx : Filter.IsBoundedUnder (· ≤ ·) atTop x)
    (hy : Filter.IsBoundedUnder (· ≤ ·) atTop y) :
    limsup (x + y) atTop ≤ limsup x atTop + limsup y atTop := by
  sorry

end Problem17

-- ============================================================================
-- Problem 18 (§3.7 #15)
-- Cauchy Condensation Test: ∑ a(n) converges ↔ ∑ 2ⁿ a(2ⁿ) converges,
-- for (a(n)) decreasing and positive.
-- ============================================================================

section Problem18

theorem problem18 {a : ℕ → ℝ}
    (hpos : ∀ n, 0 < a n)
    (hdecr : Antitone a) :
    Summable a ↔ Summable (fun n => 2 ^ n * a (2 ^ n)) := by
  sorry

end Problem18

-- ============================================================================
-- Problem 19 (§4.1 #15)
-- f(x) = x if x ∈ ℚ, 0 otherwise.
-- (a) lim_{x→0} f(x) = 0.
-- (b) For c ≠ 0, lim_{x→c} f(x) does not exist.
-- ============================================================================

section Problem19

noncomputable def f19 (x : ℝ) : ℝ :=
  if ∃ q : ℚ, (q : ℝ) = x then x else 0

theorem problem19a : Filter.Tendsto f19 (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨ε, hε, fun x hx hxd => ?_⟩
  simp only [f19]
  split_ifs with h
  · simpa [Real.dist_eq] using hxd
  · simp [dist_self]

theorem problem19b (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ l, Filter.Tendsto f19 (nhdsWithin c {c}ᶜ) (nhds l) := by
  sorry

end Problem19

-- ============================================================================
-- Problem 20 (§4.2 #5)
-- If f is bounded near c and lim_{x→c} g(x) = 0, then lim_{x→c} f(x)g(x) = 0.
-- ============================================================================

section Problem20

theorem problem20 {A : Set ℝ} {c : ℝ} {f g : ℝ → ℝ}
    (hfbdd : ∃ M > 0, ∃ δ > 0, ∀ x ∈ A, dist x c < δ → |f x| ≤ M)
    (hglim : Filter.Tendsto g (nhdsWithin c A) (nhds 0)) :
    Filter.Tendsto (fun x => f x * g x) (nhdsWithin c A) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hglim ⊢
  obtain ⟨M, hM, δ₁, hδ₁, hfM⟩ := hfbdd
  intro ε hε
  obtain ⟨δ₂, hδ₂, hg⟩ := hglim (ε / M) (div_pos hε hM)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hxA hxd => ?_⟩
  have hxδ₁ : dist x c < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxδ₂ : dist x c < δ₂ := lt_of_lt_of_le hxd (min_le_right _ _)
  have hfx : |f x| ≤ M := hfM x hxA hxδ₁
  have hgx : dist (g x) 0 < ε / M := hg x hxA hxδ₂
  rw [Real.dist_eq, sub_zero] at hgx
  rw [Real.dist_eq, sub_zero]
  calc |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ M * |g x| := by apply mul_le_mul_of_nonneg_right hfx (abs_nonneg _)
    _ < M * (ε / M) := by apply mul_lt_mul_of_pos_left hgx hM
    _ = ε := by field_simp

end Problem20

/-
  Problem 1.
  Let A ⊆ ℝ, c ∈ A, and f : A → ℝ be continuous at c.
  Prove: ∀ ε > 0, ∃ δ > 0, ∀ x y ∈ A ∩ Vδ(c), |f x - f y| < ε.
-/

section Problem21

variable {A : Set ℝ} {c : ℝ} {f : A → ℝ}

/-- Continuity at `c` in the subspace `A` implies a uniform
    continuity-type statement in a small neighborhood of `c`. -/
theorem problem21
    (hc : c ∈ A)
    (hcont : ContinuousAt f ⟨c, hc⟩) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ ⦃x y : ℝ⦄, (hx : x ∈ A) → (hy : y ∈ A) →
        dist x c < δ → dist y c < δ →
        |f ⟨x, hx⟩ - f ⟨y, hy⟩| < ε := by
  intro ε hε
  have hcont' := (Metric.continuousAt_iff.1 hcont)
  have hε2 : 0 < ε / 2 := by nlinarith
  rcases hcont' (ε / 2) hε2 with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy hxδ hyδ
  have hx' : dist (f ⟨x, hx⟩) (f ⟨c, hc⟩) < ε / 2 := by
    have : dist (⟨x, hx⟩ : A) ⟨c, hc⟩ < δ := by
      simpa [Subtype.dist_eq] using hxδ
    simpa using (hδ (x := (⟨x, hx⟩ : A)) this)
  have hy' : dist (f ⟨y, hy⟩) (f ⟨c, hc⟩) < ε / 2 := by
    have : dist (⟨y, hy⟩ : A) ⟨c, hc⟩ < δ := by
      simpa [Subtype.dist_eq] using hyδ
    simpa using (hδ (x := (⟨y, hy⟩ : A)) this)
  have hx'' : |f ⟨x, hx⟩ - f ⟨c, hc⟩| < ε / 2 := by
    simpa [Real.dist_eq] using hx'
  have hy'' : |f ⟨y, hy⟩ - f ⟨c, hc⟩| < ε / 2 := by
    simpa [Real.dist_eq] using hy'
  have hle :
      |f ⟨x, hx⟩ - f ⟨y, hy⟩|
        ≤ |f ⟨x, hx⟩ - f ⟨c, hc⟩| + |f ⟨y, hy⟩ - f ⟨c, hc⟩| := by
    -- `abs_sub_le` gives `|a - c| ≤ |a - b| + |b - c|`
    have := abs_sub_le (f ⟨x, hx⟩) (f ⟨c, hc⟩) (f ⟨y, hy⟩)
    -- rewrite `|f c - f y|` to `|f y - f c|`
    simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using this
  have hlt :
      |f ⟨x, hx⟩ - f ⟨y, hy⟩|
        < ε / 2 + ε / 2 := by
    exact lt_of_le_of_lt hle (add_lt_add hx'' hy'')
  -- `ε/2 + ε/2 = ε`
  have : (ε / 2 + ε / 2 : ℝ) = ε := by ring
  simpa [this] using hlt

end Problem21

/-
  Problem 22.
  Let L > 0 and suppose f : ℝ → ℝ satisfies
  |f x - f y| ≤ L * |x - y| for all x, y.
  Prove: f is continuous on ℝ.
-/

section Problem22

variable {L : ℝ} {f : ℝ → ℝ}

/-- A Lipschitz function `ℝ → ℝ` is continuous everywhere. -/
theorem problem22
    (Lpos : 0 < L)
    (hLip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) :
    Continuous f := by
  -- direct ε-δ proof
  refine continuous_iff_continuousAt.2 ?_
  intro x0
  refine Metric.continuousAt_iff.2 ?_
  intro ε hε
  refine ⟨ε / L, div_pos hε Lpos, ?_⟩
  intro x hx
  have hx' : |x - x0| < ε / L := by
    simpa [Real.dist_eq, abs_sub_comm] using hx
  have hfx : |f x - f x0| ≤ L * |x - x0| := by
    simpa [abs_sub_comm] using hLip x x0
  have : L * |x - x0| < ε := by
    have hL : 0 < L := Lpos
    have := mul_lt_mul_of_pos_left hx' hL
    -- `L * (ε / L) = ε`
    have hLeq : L * (ε / L) = ε := by
      field_simp [hL.ne']
    simpa [hLeq, mul_assoc] using this
  have : |f x - f x0| < ε := lt_of_le_of_lt hfx this
  simpa [Real.dist_eq, abs_sub_comm] using this

end Problem22

/-
  Problem 23.
  Let f : ℝ → ℝ be continuous, and P := {x : ℝ | f x > 0}.
  Show: if c ∈ P, then ∃ δ > 0, Vδ(c) ⊆ P.
-/

section Problem23

variable {f : ℝ → ℝ}

/-- If `f` is continuous and `f c > 0`, then `f` is positive
    in some neighborhood of `c`. -/
theorem problem23
    (hcont : Continuous f)
    {c : ℝ}
    (hc : f c > 0) :
    ∃ δ > (0 : ℝ), ∀ x, dist x c < δ → f x > 0 := by
  -- continuity at `c`, with ε = (f c)/2
  have hcontc : ContinuousAt f c := hcont.continuousAt
  have hcontc' := Metric.continuousAt_iff.1 hcontc
  have hε : 0 < f c / 2 := by nlinarith
  rcases hcontc' (f c / 2) hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hxδ
  have hx' : dist (f x) (f c) < f c / 2 := hδ (x := x) hxδ
  have hx'' : |f x - f c| < f c / 2 := by
    simpa [Real.dist_eq] using hx'
  have hineq : -(f c / 2) < f x - f c := (abs_lt.1 (by
    simpa [sub_eq_add_neg, abs_sub_comm, add_comm, add_left_comm, add_assoc] using hx'')).1
  -- from `-(f c/2) < f x - f c` we get `f c/2 < f x`
  nlinarith

/-- In set language: `P = {x | f x > 0}` is open near points where `f` is positive. -/
theorem problem23_set
    (hcont : Continuous f)
    {c : ℝ}
    (hc : f c > 0) :
    ∃ δ > (0 : ℝ), ball c δ ⊆ {x : ℝ | f x > 0} := by
  rcases problem23 hcont hc with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  have hx' : dist x c < δ := by
    simpa [ball, mem_setOf_eq] using hx
  exact hδ x hx'

end Problem23

/-
  Problem 24.
  A function f : ℝ → ℝ is additive if
  f (x + y) = f x + f y for all x, y.
  Prove: if f is additive and continuous, then
  f x = c * x for every x, where c = f 1.
-/

section Problem24

variable {f : ℝ → ℝ}

/-- Additive function on `ℝ` plus continuity implies linearity. -/
theorem problem24
    (hadd : ∀ x y : ℝ, f (x + y) = f x + f y)
    (hcont : Continuous f) :
    ∀ x, f x = f 1 * x := by
  -- package `hadd` as an additive homomorphism, then use mathlib's theorem
  -- that a continuous additive map between real vector spaces is `ℝ`-linear.
  let fAdd : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        have h' : f 0 = f 0 + f 0 := by simpa using h
        have := congrArg (fun t => t - f 0) h'
        -- `this : 0 = f 0`
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
      map_add' := hadd }
  have hfLin : Continuous fAdd := hcont
  let fLin : ℝ →L[ℝ] ℝ := AddMonoidHom.toRealLinearMap fAdd hfLin
  intro x
  -- `x = x • 1` and linearity gives `f x = x • f 1 = f 1 * x`
  have hx : fLin x = x • fLin 1 := by
    simpa using (fLin.map_smul x (1 : ℝ))
  -- unfold back to `f`
  -- `•` on `ℝ` is multiplication
  simpa [fAdd, fLin, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hx

end Problem24
