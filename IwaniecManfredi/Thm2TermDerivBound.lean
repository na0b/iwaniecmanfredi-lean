import IwaniecManfredi.Thm2TermWirtingerDerivs
import IwaniecManfredi.LambdaEpsEstimates
set_option maxHeartbeats 1000000

/-- The uniform pointwise bound on the two Wirtinger derivatives of a single
summand of the series (19): for `n ≥ 1`, `1 < p < ∞`, every `m ≥ 0` and every
`ξ ≠ 0`, both `‖(T_{n+m})_ξ(ξ)‖` and `‖(T_{n+m})_{ξ̄}(ξ)‖` are at most
`(4 + √(p-1)) · (n + m) · ‖A_{n+m}‖ · ‖ξ‖^{λ_{n+m} - 1}`.

What matters is that the constant `4 + √(p-1)` does not depend on `m`: the
only `m`-dependence left is the explicit factor `n + m` and the explicit power
`‖ξ‖^{λ_{n+m}-1}`.  That uniformity comes entirely from the Remark's estimates
(23)-(25), carried by `LambdaEpsEstimates`: `0 ≤ λ_{n+m} ≤ (n+m)√(p-1)` and
`|ε_{n+m}| ≤ 1`.  Without the upper bound on `λ_k` the coefficients of the
closed form would grow with `k` at an unknown rate and no uniform constant
would exist.

This is the pointwise estimate the `W^{1,2}` convergence argument needs before
it can sum over `k`: paired with the geometric decay of `‖ξ‖^{λ_{n+m}}` on a
disc of radius `ρ < 1` it makes the tail of the differentiated series dominated
by a convergent one, which is what lets the series (19) be differentiated
term by term in the `W^{1,2}` norm.

The family is indexed by `m` with `k = n + m`, matching the shape in which
`LambdaEpsEstimates` is applied throughout: all three estimates it supplies
are statements about `LambdaCoef n (n + m) p` and `EpsCoef n (n + m) p`. -/
theorem Thm2TermDerivBound (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (A : ℤ → ℂ)
    (m : ℕ) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ‖DZ (Thm2Term n p A (n + m)) ξ‖
        ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
          * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)
    ∧ ‖DZbar (Thm2Term n p A (n + m)) ξ‖
        ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
          * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
  -- the estimates (23)-(25) of the Remark, in the `n + m` shape used below
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  have hcast : ∀ m : ℕ, (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := by
    intro m; push_cast; ring
  -- `λ_{n+m} ≥ 0`, `|ε_{n+m}| ≤ 1`, `λ_{n+m} ≤ (n+m)√(p-1)`
  have hL0 : ∀ m : ℕ, 0 ≤ LambdaCoef n (n + m) p := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
    · have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
  have hepsle : ∀ m : ℕ, |EpsCoef n (n + m) p| ≤ 1 := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hepsn]; norm_num
    · exact (hepsbd (n + m) (by omega)).le
  have hLup : ∀ m : ℕ, LambdaCoef n (n + m) p ≤ ((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
      have hs : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
      have : (0 : ℝ) ≤ (n : ℝ) + ((0 : ℕ) : ℝ) := by positivity
      exact mul_nonneg this hs
    · have h2 := (hlambd (n + m) (by omega)).2
      rw [hcast m] at h2
      exact h2
  have hthree : ∀ (k : ℕ) (ξ : ℂ),
      ‖A (k : ℤ) * ξ ^ k‖ ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) ∧
      ‖((EpsCoef n k p : ℝ) : ℂ) * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) ∧
      ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ)
            * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
    intro k ξ
    have hrk : (0 : ℝ) ≤ ‖ξ‖ ^ (k : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hprod : (0 : ℝ) ≤ ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := mul_nonneg (norm_nonneg _) hrk
    have hone' : (1 : ℝ) ≤ 1 + |EpsCoef n k p| := by
      have := abs_nonneg (EpsCoef n k p)
      linarith
    have h1 : ‖A (k : ℤ) * ξ ^ k‖ = ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
      rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖ξ‖ k]
    have h2 : ‖((EpsCoef n k p : ℝ) : ℂ)
          * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
        = |EpsCoef n k p| * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, ← Real.rpow_natCast ‖ξ‖ k]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      calc ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) = 1 * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) := by ring
        _ ≤ (1 + |EpsCoef n k p|) * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hone' hprod
        _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by ring
    · rw [h2]
      calc |EpsCoef n k p| * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ))
          ≤ (1 + |EpsCoef n k p|) * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hprod
        _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by ring
    · refine le_trans (norm_add_le _ _) ?_
      rw [h1, h2]
      exact le_of_eq (by ring)
  have hbdgen : ∀ (c1 c2 X1 X2 : ℂ) (W : ℝ), ‖X1‖ ≤ W → ‖X2‖ ≤ W →
      ‖c1 * X1 + c2 * X2‖ ≤ (‖c1‖ + ‖c2‖) * W := by
    intro c1 c2 X1 X2 W h1 h2
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have k1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg c1)
    have k2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg c2)
    have hexp : (‖c1‖ + ‖c2‖) * W = ‖c1‖ * W + ‖c2‖ * W := by ring
    rw [hexp]
    linarith
  have hnMuN : ∀ k : ℕ,
      ‖((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ)‖
        = |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)| := by
    intro k
    rw [show ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ)
        = (((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ) : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have hnMuh : ∀ k : ℕ, ‖((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2‖
      = |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2| := by
    intro k
    rw [show ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2
        = (((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
  have hconstbd : ∀ m : ℕ,
      ((((n : ℝ) + (m : ℝ)) + |(LambdaCoef n (n + m) p + (n : ℝ) - ((n : ℝ) + (m : ℝ))) / 2
            - (n : ℝ)|) * (1 + |EpsCoef n (n + m) p|)
          ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)))
      ∧ ((((n : ℝ) + (m : ℝ)) + |(LambdaCoef n (n + m) p + (n : ℝ) - ((n : ℝ) + (m : ℝ))) / 2|)
            * (1 + |EpsCoef n (n + m) p|)
          ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ))) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hkk : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by linarith
    have hl0 := hL0 m
    have hlup := hLup m
    have he := hepsle m
    have he0 := abs_nonneg (EpsCoef n (n + m) p)
    have hb1 : |(LambdaCoef n (n + m) p + (n : ℝ) - ((n : ℝ) + (m : ℝ))) / 2 - (n : ℝ)|
        ≤ (((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) + 2 * ((n : ℝ) + (m : ℝ))) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    have hb2 : |(LambdaCoef n (n + m) p + (n : ℝ) - ((n : ℝ) + (m : ℝ))) / 2|
        ≤ (((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) + 2 * ((n : ℝ) + (m : ℝ))) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    exact ⟨by nlinarith, by nlinarith⟩
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hcastA : A (((n + m : ℕ)) : ℤ) = A ((n : ℤ) + (m : ℤ)) := by congr 1
  have hcastk : (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := hcast m
  have hw := Thm2TermWirtingerDerivs n p A (n + m) ξ hξ
  have hgn : ‖((‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) : ℝ) : ℂ)‖
      = ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _)]
  have hpp : ‖ξ ^ (-(n : ℤ))‖ = ‖ξ‖ ^ (-(n : ℝ)) := by
    rw [norm_zpow, ← Real.rpow_intCast ‖ξ‖ (-(n : ℤ))]
    norm_num
  have hrid : ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
        * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ)
      = ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one ‖ξ‖, ← Real.rpow_add hr, ← Real.rpow_add hr,
      ← Real.rpow_add hr]
    congr 1
    ring
  have hWnn : (0 : ℝ) ≤ (1 + |EpsCoef n (n + m) p|) * ‖A (((n + m : ℕ)) : ℤ)‖
      * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ) := by
    have := abs_nonneg (EpsCoef n (n + m) p)
    have h2 : (0 : ℝ) ≤ ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    positivity
  have hfacx : ‖((‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) : ℝ) : ℂ)
        * ξ ^ (-(n : ℤ)) / ξ‖
      = ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
          * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ := by
    rw [norm_div, norm_mul, hgn, hpp]
  have hfacy : ‖((‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) : ℝ) : ℂ)
        * ξ ^ (-(n : ℤ)) / starRingEnd ℂ ξ‖
      = ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
          * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ := by
    rw [norm_div, norm_mul, hgn, hpp, Complex.norm_conj]
  have hfacnn : (0 : ℝ)
      ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
          * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ := by
    have h1 : (0 : ℝ)
        ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (0 : ℝ) ≤ ‖ξ‖ ^ (-(n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    positivity
  have hcb := hconstbd m
  constructor
  · rw [hw.1, norm_mul, hfacx]
    have hbr0 := hbdgen (((n + m : ℕ)) : ℂ)
      ((((LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ)))
      _ _ _ (hthree (n + m) ξ).1 (hthree (n + m) ξ).2.2
    rw [Complex.norm_natCast, hnMuN (n + m)] at hbr0
    have hbr := hbr0
    calc ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
            * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖
          * ‖(((n + m : ℕ)) : ℂ) * (A (((n + m : ℕ)) : ℤ) * ξ ^ (n + m))
            + (((LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ) : ℝ) : ℂ) / 2
                - (n : ℂ))
              * (A (((n + m : ℕ)) : ℤ) * ξ ^ (n + m)
                + ((EpsCoef n (n + m) p : ℝ) : ℂ)
                    * (starRingEnd ℂ (A (((n + m : ℕ)) : ℤ))
                      * (starRingEnd ℂ ξ) ^ (n + m)))‖
        ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
              * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖
            * ((((((n + m : ℕ))) : ℝ)
                  + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2 - (n : ℝ)|)
                * ((1 + |EpsCoef n (n + m) p|) * ‖A (((n + m : ℕ)) : ℤ)‖
                    * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ))) :=
          mul_le_mul_of_nonneg_left hbr hfacnn
      _ = ((((((n + m : ℕ))) : ℝ)
                + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2 - (n : ℝ)|)
              * (1 + |EpsCoef n (n + m) p|)) * ‖A (((n + m : ℕ)) : ℤ)‖
            * (‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
                * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ)) := by ring
      _ = ((((((n + m : ℕ))) : ℝ)
                + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2 - (n : ℝ)|)
              * (1 + |EpsCoef n (n + m) p|)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
          rw [hrid, hcastA]
      _ ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
          rw [hcastk]
          have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
          have hp1 : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) :=
            Real.rpow_nonneg (norm_nonneg _) _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcb.1 hA0) hp1
  · rw [hw.2, norm_mul, hfacy]
    have hbr0 := hbdgen (((n + m : ℕ)) : ℂ)
      ((((LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ) : ℝ) : ℂ) / 2))
      _ _ _ (hthree (n + m) ξ).2.1 (hthree (n + m) ξ).2.2
    rw [Complex.norm_natCast, hnMuh (n + m)] at hbr0
    have hbr := hbr0
    calc ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
            * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖
          * ‖(((n + m : ℕ)) : ℂ) * (((EpsCoef n (n + m) p : ℝ) : ℂ)
                * (starRingEnd ℂ (A (((n + m : ℕ)) : ℤ)) * (starRingEnd ℂ ξ) ^ (n + m)))
            + (((LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ) : ℝ) : ℂ) / 2)
              * (A (((n + m : ℕ)) : ℤ) * ξ ^ (n + m)
                + ((EpsCoef n (n + m) p : ℝ) : ℂ)
                    * (starRingEnd ℂ (A (((n + m : ℕ)) : ℤ))
                      * (starRingEnd ℂ ξ) ^ (n + m)))‖
        ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
              * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖
            * ((((((n + m : ℕ))) : ℝ)
                  + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2|)
                * ((1 + |EpsCoef n (n + m) p|) * ‖A (((n + m : ℕ)) : ℤ)‖
                    * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ))) :=
          mul_le_mul_of_nonneg_left hbr hfacnn
      _ = ((((((n + m : ℕ))) : ℝ)
                + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2|)
              * (1 + |EpsCoef n (n + m) p|)) * ‖A (((n + m : ℕ)) : ℤ)‖
            * (‖ξ‖ ^ (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ))
                * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ * ‖ξ‖ ^ ((((n + m : ℕ))) : ℝ)) := by ring
      _ = ((((((n + m : ℕ))) : ℝ)
                + |(LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2|)
              * (1 + |EpsCoef n (n + m) p|)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
          rw [hrid, hcastA]
      _ ≤ (4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) := by
          rw [hcastk]
          have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
          have hp1 : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) :=
            Real.rpow_nonneg (norm_nonneg _) _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcb.2 hA0) hp1
