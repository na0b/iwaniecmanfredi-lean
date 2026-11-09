import IwaniecManfredi.LambdaCoef
import IwaniecManfredi.GammaExp
import IwaniecManfredi.DExp

/-- The identity `d(p) = 1/γ_1(p)` of Section 6 of the paper: the exponent
`d = d(p)` displayed in (50) is the reciprocal of `γ_1 = λ_2(1,p)`, which by
`GammaRatioMinAtOne` is the smallest of the numbers `n/γ_n`. -/
theorem DExpEqGammaOneInv (p : ℝ) (hp : 1 < p) :
    0 < GammaExp 1 p ∧ GammaExp 1 p * DExp p = 1 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hp1ne : p - 1 ≠ 0 := ne_of_gt hp1
  -- ## Step 2 (first half): the radicand is positive
  have hrad : (0 : ℝ) < p ^ 2 + 12 * p - 12 := by nlinarith [sq_nonneg p]
  obtain ⟨S, hS⟩ : ∃ x : ℝ, x = Real.sqrt (p ^ 2 + 12 * p - 12) := ⟨_, rfl⟩
  have hS2 : S ^ 2 = p ^ 2 + 12 * p - 12 := by
    rw [hS]
    exact Real.sq_sqrt hrad.le
  have hSp : p < S := by
    rw [hS, Real.lt_sqrt hp0.le]
    linarith
  -- ## Step 1: the closed form for `γ₁`
  have hg1 : GammaExp 1 p = (-p + S) / 2 := by
    rw [hS, GammaExp, LambdaCoef]
    have h : 4 * ((1 + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + ((1 : ℕ) : ℝ) ^ 2 * (p - 2) ^ 2
        = p ^ 2 + 12 * p - 12 := by
      push_cast
      ring
    rw [h]
    push_cast
    ring
  -- ## Step 3: the closed form for `d`
  have hinner : 1 + 14 / (p - 1) + 1 / (p - 1) ^ 2
      = (p ^ 2 + 12 * p - 12) / (p - 1) ^ 2 := by
    field_simp
    ring
  have hsq : Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2) = S / (p - 1) := by
    rw [hinner, Real.sqrt_div hrad.le, Real.sqrt_sq hp1.le, hS]
  have hd : DExp p = (p + S) / (6 * (p - 1)) := by
    rw [DExp, hsq]
    field_simp
    ring
  -- ## Step 4: the product
  refine ⟨by rw [hg1]; linarith, ?_⟩
  rw [hg1, hd]
  field_simp
  linear_combination hS2
