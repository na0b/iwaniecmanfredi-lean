import IwaniecManfredi.LambdaCoef
import IwaniecManfredi.GammaExp

/-- The sharp linear lower bound on `λ_k(n,p)`, with equality at `k = n+1`:
for `k ≥ n+1`, `λ_k(n,p) ≥ (γ_n/(n+1)) k`.  This is the strengthening of the
lower bound of (25) that the proof of (22) in Theorem 2 requires: (22) needs
`Σ k|A_k|²` to be controlled by `Σ λ_k|A_k|²`, which the constant lower bound
of (25) does not supply. -/
theorem LambdaLinearLowerBound (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) :
    ∀ k : ℕ, n + 1 ≤ k →
      GammaExp n p / ((n : ℝ) + 1) * (k : ℝ) ≤ LambdaCoef n k p := by
  -- Basic positivity facts.  Throughout, `A = 4(p-1) > 0` and
  -- `B = n²(p-2)² ≥ 0` are written out inline, and
  -- `g t = -(n p) t + √(A + B t²)`.
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hnp : (0 : ℝ) < (n : ℝ) * p := by positivity
  -- Step 1: `B t ≤ n p √(A + B t²)` for `t ≥ 0`.
  have step1 : ∀ t : ℝ, 0 ≤ t →
      (n : ℝ) ^ 2 * (p - 2) ^ 2 * t
        ≤ (n : ℝ) * p * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2) := by
    intro t ht
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2 := by positivity
    have hrad : (0 : ℝ) ≤ 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2 := by linarith
    have hs2 : Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2) ^ 2
        = 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2 := Real.sq_sqrt hrad
    have hs0 : (0 : ℝ) ≤ Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2) :=
      Real.sqrt_nonneg _
    have hL0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 * t := by positivity
    have hR0 : (0 : ℝ)
        ≤ (n : ℝ) * p * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2) :=
      mul_nonneg hnp.le hs0
    -- Compare the squares: the difference is `4(p-1)(n²p² + n⁴(p-2)²t²) ≥ 0`.
    have hid : ((n : ℝ) * p * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2)) ^ 2
          - ((n : ℝ) ^ 2 * (p - 2) ^ 2 * t) ^ 2
        = 4 * (p - 1) * ((n : ℝ) ^ 2 * p ^ 2 + (n : ℝ) ^ 4 * (p - 2) ^ 2 * t ^ 2) := by
      linear_combination ((n : ℝ) * p) ^ 2 * hs2
    have hsq : ((n : ℝ) ^ 2 * (p - 2) ^ 2 * t) ^ 2
        ≤ ((n : ℝ) * p * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2)) ^ 2 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * p ^ 2 + (n : ℝ) ^ 4 * (p - 2) ^ 2 * t ^ 2 := by
        positivity
      nlinarith [hid, mul_nonneg hp1.le hnn]
    calc (n : ℝ) ^ 2 * (p - 2) ^ 2 * t
        = Real.sqrt (((n : ℝ) ^ 2 * (p - 2) ^ 2 * t) ^ 2) := (Real.sqrt_sq hL0).symm
      _ ≤ Real.sqrt (((n : ℝ) * p
            * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = (n : ℝ) * p * Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t ^ 2) :=
          Real.sqrt_sq hR0
  -- Step 2: `g` is nonincreasing on `[0, ∞)`.
  have step2 : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
      -((n : ℝ) * p) * t₂ + Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2)
        ≤ -((n : ℝ) * p) * t₁
            + Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2) := by
    intro t₁ t₂ h1 h12
    have h2' : (0 : ℝ) ≤ t₂ := le_trans h1 h12
    have e₁ := step1 t₁ h1
    have e₂ := step1 t₂ h2'
    have hz₁ : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2 := by positivity
    have hz₂ : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2 := by positivity
    have hr₁ : (0 : ℝ) < 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2 := by linarith
    have hr₂ : (0 : ℝ) < 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2 := by linarith
    have hs₁2 : Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2) ^ 2
        = 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2 := Real.sq_sqrt hr₁.le
    have hs₂2 : Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2) ^ 2
        = 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2 := Real.sq_sqrt hr₂.le
    have hp₁ : (0 : ℝ) < Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2) :=
      Real.sqrt_pos.mpr hr₁
    have hp₂ : (0 : ℝ) < Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2) :=
      Real.sqrt_pos.mpr hr₂
    set s₁ := Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₁ ^ 2) with hsd₁
    set s₂ := Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * t₂ ^ 2) with hsd₂
    -- Rationalise the difference of the two square roots.
    have hdiff : (s₂ - s₁) * (s₁ + s₂)
        = (n : ℝ) ^ 2 * (p - 2) ^ 2 * (t₁ + t₂) * (t₂ - t₁) := by
      linear_combination hs₂2 - hs₁2
    have hsum : (n : ℝ) ^ 2 * (p - 2) ^ 2 * (t₁ + t₂) ≤ (n : ℝ) * p * (s₁ + s₂) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr h12)
    have hkey : (s₂ - s₁) * (s₁ + s₂) ≤ ((n : ℝ) * p * (t₂ - t₁)) * (s₁ + s₂) := by
      rw [hdiff]; linarith [hmul]
    have hfin := le_of_mul_le_mul_right hkey (by linarith : (0 : ℝ) < s₁ + s₂)
    linarith
  -- Step 3: the rescaling identity `√(A + B/c²) = √(A c² + B)/c` for `c > 0`.
  have step3 : ∀ c : ℝ, 0 < c →
      Real.sqrt (4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * (1 / c) ^ 2)
        = Real.sqrt (4 * c ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) / c := by
    intro c hc
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 := by positivity
    have hR : (0 : ℝ) ≤ 4 * c ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg c) hp1.le, h0]
    have hcne : c ≠ 0 := ne_of_gt hc
    have hrw : 4 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 * (1 / c) ^ 2
        = (4 * c ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) * (1 / c) ^ 2 := by
      field_simp
    rw [hrw, Real.sqrt_mul hR, Real.sqrt_sq (one_div_pos.mpr hc).le]
    ring
  -- Step 4: apply Step 2 with `t₁ = 1/k`, `t₂ = 1/(n+1)` and rewrite by Step 3.
  intro k hk
  have hkR : ((n : ℝ) + 1) ≤ (k : ℝ) := by
    have h : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    push_cast at h
    exact h
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hK : (0 : ℝ) < (k : ℝ) := by linarith
  have hinv : 1 / (k : ℝ) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hN hkR
  have hinv0 : (0 : ℝ) ≤ 1 / (k : ℝ) := (one_div_pos.mpr hK).le
  have h2 := step2 (1 / (k : ℝ)) (1 / ((n : ℝ) + 1)) hinv0 hinv
  rw [step3 (k : ℝ) hK, step3 ((n : ℝ) + 1) hN] at h2
  have h : (-((n : ℝ) * p)
        + Real.sqrt (4 * ((n : ℝ) + 1) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2))
          / ((n : ℝ) + 1)
      ≤ (-((n : ℝ) * p)
        + Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)) / (k : ℝ) := by
    have e1 : (-((n : ℝ) * p)
          + Real.sqrt (4 * ((n : ℝ) + 1) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2))
            / ((n : ℝ) + 1)
        = -((n : ℝ) * p) * (1 / ((n : ℝ) + 1))
          + Real.sqrt (4 * ((n : ℝ) + 1) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
            / ((n : ℝ) + 1) := by ring
    have e2 : (-((n : ℝ) * p)
          + Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)) / (k : ℝ)
        = -((n : ℝ) * p) * (1 / (k : ℝ))
          + Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
            / (k : ℝ) := by ring
    rw [e1, e2]
    exact h2
  have hcross := (div_le_div_iff₀ hN hK).mp h
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  unfold GammaExp LambdaCoef
  push_cast
  linarith [hcross]
