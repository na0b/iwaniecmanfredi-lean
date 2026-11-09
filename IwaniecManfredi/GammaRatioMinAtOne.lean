import IwaniecManfredi.LambdaCoef
import IwaniecManfredi.GammaExp

/-- The assertion of Section 6 of the paper that `γ_n > 0` and that the
smallest of the numbers `n/γ_n`, `n = 1, 2, …`, occurs at `n = 1`.  This is
what licenses Section 6 to pass from the `n`-dependent estimate (48) of
Corollary 2 to the estimates (51), (52), which are independent of `n`. -/
theorem GammaRatioMinAtOne (p : ℝ) (hp : 1 < p) :
    (∀ n : ℕ, 1 ≤ n → 0 < GammaExp n p) ∧
      ∀ n : ℕ, 1 ≤ n → 1 / GammaExp 1 p ≤ (n : ℝ) / GammaExp n p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  -- Step 2: the scale-free form of the radical, stated for a real `c > 0`
  -- so that no `((n+1 : ℕ) : ℝ)` casts have to be reconciled.
  have step2 : ∀ c : ℝ, 0 < c →
      Real.sqrt (4 * (c + 1) ^ 2 * (p - 1) + c ^ 2 * (p - 2) ^ 2)
        = c * Real.sqrt (4 * (1 + 1 / c) ^ 2 * (p - 1) + (p - 2) ^ 2) := by
    intro c hc
    have h1 : (0 : ℝ) ≤ 4 * (1 + 1 / c) ^ 2 * (p - 1) :=
      mul_nonneg (by positivity) hp1.le
    have hR : (0 : ℝ) ≤ 4 * (1 + 1 / c) ^ 2 * (p - 1) + (p - 2) ^ 2 := by
      nlinarith [sq_nonneg (p - 2)]
    have hcne : c ≠ 0 := ne_of_gt hc
    have hrw : 4 * (c + 1) ^ 2 * (p - 1) + c ^ 2 * (p - 2) ^ 2
        = (4 * (1 + 1 / c) ^ 2 * (p - 1) + (p - 2) ^ 2) * c ^ 2 := by
      field_simp
    rw [hrw, Real.sqrt_mul hR, Real.sqrt_sq hc.le]
    ring
  -- `2 γ_n = n (-p + √(4(1+1/n)²(p-1) + (p-2)²))`.
  have hform : ∀ n : ℕ, 1 ≤ n →
      2 * GammaExp n p
        = (n : ℝ) * (-p + Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have h := step2 (n : ℝ) hn0
    unfold GammaExp LambdaCoef
    push_cast
    rw [h]
    ring
  -- The case `n = 1`, where `4(1 + 1/1)² = 16`.
  have hg1 : 2 * GammaExp 1 p = -p + Real.sqrt (16 * (p - 1) + (p - 2) ^ 2) := by
    have h := hform 1 le_rfl
    rw [h]
    norm_num
  -- Step 3: monotonicity of the radicand in `1/n`.
  have hmono : ∀ n : ℕ, 1 ≤ n →
      Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)
        ≤ Real.sqrt (16 * (p - 1) + (p - 2) ^ 2) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    apply Real.sqrt_le_sqrt
    have hinv0 : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hn0
    have hinv1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hn1
    have hsq : (1 + 1 / (n : ℝ)) ^ 2 ≤ 4 := by nlinarith
    linarith [mul_le_mul_of_nonneg_right hsq hp1.le]
  -- Step 1: part (a).
  have parta : ∀ n : ℕ, 1 ≤ n → 0 < GammaExp n p := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hnp : (0 : ℝ) < (n : ℝ) * p := mul_pos hn0 hp0
    -- `R n - (n p)² = 4(p-1)(2n+1) > 0`.
    have hlt : ((n : ℝ) * p) ^ 2
        < 4 * ((n : ℝ) + 1) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      nlinarith [mul_pos hp1 (show (0 : ℝ) < 2 * (n : ℝ) + 1 by linarith)]
    have h := Real.sqrt_lt_sqrt (by positivity) hlt
    rw [Real.sqrt_sq hnp.le] at h
    unfold GammaExp LambdaCoef
    push_cast
    linarith
  refine ⟨parta, ?_⟩
  -- Step 4: part (b), by taking reciprocals of positives.
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgn := parta n hn
  have hgone := parta 1 le_rfl
  have hA := hform n hn
  have hM := hmono n hn
  have hg1n : (n : ℝ) * (2 * GammaExp 1 p)
      = (n : ℝ) * (-p + Real.sqrt (16 * (p - 1) + (p - 2) ^ 2)) := by rw [hg1]
  have hprod : (0 : ℝ) ≤ (n : ℝ) *
      (Real.sqrt (16 * (p - 1) + (p - 2) ^ 2)
        - Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have hle : GammaExp n p ≤ (n : ℝ) * GammaExp 1 p := by linarith
  rw [div_le_div_iff₀ hgone hgn]
  linarith
