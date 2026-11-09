import IwaniecManfredi.LambdaCoef
import IwaniecManfredi.EpsCoef

/-- The Remark following Theorem 2: estimates (23), (24) and (25) for the
numbers `λ_k(n,p)` and `ε_k(n,p)`. -/
theorem LambdaEpsEstimates (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) :
    LambdaCoef n n p = 0 ∧ EpsCoef n n p = 0 ∧
    (∀ k : ℕ, n + 1 ≤ k → |EpsCoef n k p| < 1) ∧
    (∀ k : ℕ, n + 1 ≤ k →
      (p - 1) / ((n : ℝ) * p) ≤ LambdaCoef n k p ∧
        LambdaCoef n k p ≤ (k : ℝ) * Real.sqrt (p - 1)) := by
  -- Basic positivity facts: `n ≥ 1` and `p > 1`.
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hnp : (0 : ℝ) < (n : ℝ) * p := by positivity
  -- Step 1: the radicand at `k = n` is `(n p)^2`, so its square root is `n p`.
  have hsqrtn : Real.sqrt (4 * (n : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
      = (n : ℝ) * p := by
    rw [show 4 * (n : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 = ((n : ℝ) * p) ^ 2 from
      by ring]
    exact Real.sqrt_sq hnp.le
  have h23a : LambdaCoef n n p = 0 := by
    unfold LambdaCoef
    rw [hsqrtn]; ring
  -- Step 2: `ε_n = 0 / (2n) = 0`.
  have h23b : EpsCoef n n p = 0 := by
    unfold EpsCoef
    rw [h23a]
    simp
  -- Casting `n + 1 ≤ k` into `ℝ`.
  have hcast : ∀ k : ℕ, n + 1 ≤ k → ((n : ℝ) + 1) ≤ (k : ℝ) := by
    intro k hk
    have h : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    push_cast at h
    exact h
  -- Step 3: for `k ≥ n+1` the square root strictly exceeds `n p`.
  have hsqrtk : ∀ k : ℕ, n + 1 ≤ k →
      (n : ℝ) * p < Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) := by
    intro k hk
    have hk' := hcast k hk
    have hsq : (0 : ℝ) < (k : ℝ) ^ 2 - (n : ℝ) ^ 2 := by nlinarith
    have hlt : ((n : ℝ) * p) ^ 2
        < 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      nlinarith [mul_pos hp1 hsq]
    have h := Real.sqrt_lt_sqrt (by positivity) hlt
    rwa [Real.sqrt_sq hnp.le] at h
  have hpos : ∀ k : ℕ, n + 1 ≤ k → 0 < LambdaCoef n k p := by
    intro k hk
    have h := hsqrtk k hk
    unfold LambdaCoef
    linarith
  -- Step 4: estimate (24).
  have h24 : ∀ k : ℕ, n + 1 ≤ k → |EpsCoef n k p| < 1 := by
    intro k hk
    have hL := hpos k hk
    have hk' := hcast k hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hden : (0 : ℝ) < LambdaCoef n k p + (n : ℝ) + (k : ℝ) := by linarith
    unfold EpsCoef
    rw [abs_div, abs_of_pos hden, div_lt_one hden, abs_lt]
    constructor <;> linarith
  -- The auxiliary quantity `t = √(p-1)`.
  set t := Real.sqrt (p - 1) with ht_def
  have ht0 : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.mpr hp1
  have ht : t ^ 2 = p - 1 := by rw [ht_def]; exact Real.sq_sqrt hp1.le
  -- Step 5: the upper bound in (25).
  have h25ub : ∀ k : ℕ, n + 1 ≤ k → LambdaCoef n k p ≤ (k : ℝ) * t := by
    intro k hk
    have hk' := hcast k hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hid : ((n : ℝ) * p + 2 * (k : ℝ) * t) ^ 2
        - (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
        = 4 * (n : ℝ) ^ 2 * (p - 1) + 4 * ((n : ℝ) * p) * ((k : ℝ) * t) := by
      linear_combination (4 * (k : ℝ) ^ 2) * ht
    have hle : 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
        ≤ ((n : ℝ) * p + 2 * (k : ℝ) * t) ^ 2 := by
      nlinarith [hid, mul_pos hnp (mul_pos hk0 ht0), mul_nonneg (sq_nonneg (n : ℝ)) hp1.le]
    have hnn : (0 : ℝ) ≤ (n : ℝ) * p + 2 * (k : ℝ) * t := by
      nlinarith [hnp, mul_pos hk0 ht0]
    have hsq : Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
        ≤ (n : ℝ) * p + 2 * (k : ℝ) * t := by
      calc Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
          ≤ Real.sqrt (((n : ℝ) * p + 2 * (k : ℝ) * t) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (n : ℝ) * p + 2 * (k : ℝ) * t := Real.sqrt_sq hnn
    unfold LambdaCoef
    linarith
  -- Step 6: the lower bound in (25) at `k = n+1`.
  have h25lb1 : (p - 1) / ((n : ℝ) * p) ≤ LambdaCoef n (n + 1) p := by
    have hSgt := hsqrtk (n + 1) le_rfl
    set S := Real.sqrt (4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
      with hS_def
    have hrad : (0 : ℝ) ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      push_cast; nlinarith [hp1, hn1, sq_nonneg ((n : ℝ) - 2), sq_nonneg (p - 2)]
    have hS2 : S ^ 2 = 4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      rw [hS_def]; exact Real.sq_sqrt hrad
    -- The denominator bound `√R_{n+1} ≤ n p (4n+1)`.
    have hA : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) * p + 1 := by nlinarith
    have hB : (2 * (n : ℝ) + 1) * (p - 1) ≤ (2 * (n : ℝ) + 1) * p - 1 := by nlinarith
    have hB0 : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * (p - 1) := by positivity
    have hA0 : (0 : ℝ) ≤ 2 * (n : ℝ) * p + 1 := by nlinarith
    have hprod : (2 * (n : ℝ) + 1) * ((2 * (n : ℝ) + 1) * (p - 1))
        ≤ (2 * (n : ℝ) * p + 1) * ((2 * (n : ℝ) + 1) * p - 1) :=
      mul_le_mul hA hB hB0 hA0
    have hC : ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) + 1) ^ 2 := by nlinarith
    have hmain : ((n : ℝ) + 1) ^ 2 * (p - 1)
        ≤ (n : ℝ) ^ 2 * ((2 * (n : ℝ) * p + 1) * ((2 * (n : ℝ) + 1) * p - 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hprod (sq_nonneg (n : ℝ))
      have h2 := mul_le_mul_of_nonneg_right hC hp1.le
      linarith
    have hSub : S ≤ (n : ℝ) * p * (4 * (n : ℝ) + 1) := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) * p * (4 * (n : ℝ) + 1) := by positivity
      have hle : 4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
          ≤ ((n : ℝ) * p * (4 * (n : ℝ) + 1)) ^ 2 := by
        push_cast
        nlinarith [hmain]
      rw [hS_def]
      calc Real.sqrt (4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)
          ≤ Real.sqrt (((n : ℝ) * p * (4 * (n : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (n : ℝ) * p * (4 * (n : ℝ) + 1) := Real.sqrt_sq hnn
    -- Rationalise: `(S - np)(S + np) = R_{n+1} - R_n = 4(p-1)(2n+1)`.
    have hident : (S - (n : ℝ) * p) * (S + (n : ℝ) * p) = 4 * (p - 1) * (2 * (n : ℝ) + 1) := by
      have h : S ^ 2 - ((n : ℝ) * p) ^ 2 = 4 * (p - 1) * (2 * (n : ℝ) + 1) := by
        rw [hS2]; push_cast; ring
      linear_combination h
    have hSpos : (0 : ℝ) < S - (n : ℝ) * p := by linarith
    have hsum : S + (n : ℝ) * p ≤ 2 * ((n : ℝ) * p) * (2 * (n : ℝ) + 1) := by linarith [hSub]
    have hkey : 4 * (p - 1) * (2 * (n : ℝ) + 1)
        ≤ (S - (n : ℝ) * p) * (2 * ((n : ℝ) * p) * (2 * (n : ℝ) + 1)) := by
      rw [← hident]
      exact mul_le_mul_of_nonneg_left hsum hSpos.le
    have h2n1 : (0 : ℝ) < 2 * (2 * (n : ℝ) + 1) := by linarith
    have hkey2 : 2 * (2 * (n : ℝ) + 1) * (2 * (p - 1))
        ≤ 2 * (2 * (n : ℝ) + 1) * (((n : ℝ) * p) * (S - (n : ℝ) * p)) := by linarith [hkey]
    have hnp2 : 2 * (p - 1) ≤ ((n : ℝ) * p) * (S - (n : ℝ) * p) :=
      le_of_mul_le_mul_left hkey2 h2n1
    unfold LambdaCoef
    rw [hS_def] at hnp2
    rw [div_le_div_iff₀ hnp (by norm_num : (0 : ℝ) < 2)]
    linarith [hnp2]
  -- Step 7: monotonicity of `k ↦ λ_k`, transporting Step 6 to all `k ≥ n+1`.
  have hmono : ∀ k : ℕ, n + 1 ≤ k → LambdaCoef n (n + 1) p ≤ LambdaCoef n k p := by
    intro k hk
    have hk' := hcast k hk
    unfold LambdaCoef
    have hle : 4 * ((n + 1 : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
        ≤ 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      push_cast
      have hmm : ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ (k : ℝ) * (k : ℝ) :=
        mul_le_mul hk' hk' (by linarith) (by linarith)
      have hsq : (0 : ℝ) ≤ (k : ℝ) ^ 2 - ((n : ℝ) + 1) ^ 2 := by nlinarith [hmm]
      nlinarith [mul_nonneg hp1.le hsq]
    have h := Real.sqrt_le_sqrt hle
    linarith
  refine ⟨h23a, h23b, h24, fun k hk => ⟨?_, h25ub k hk⟩⟩
  exact le_trans h25lb1 (hmono k hk)
