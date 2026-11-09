import IwaniecManfredi.Thm2TermSolvesEq18
import IwaniecManfredi.LambdaLinearLowerBound
import IwaniecManfredi.GammaRatioMinAtOne
set_option maxHeartbeats 1000000

/-- The geometric summability engine behind the series (19): a positive linear
rate for the exponents `λ_k`, a uniform bound on the coefficients `A_k`, the
resulting geometric domination of `ρ^{λ_{n+m}}`, and the pointwise bound on
each summand `T_{n+m}` that the two together support.

Concretely, given the energy hypothesis `Σ_m (n+m)|A_{n+m}|² < ∞` there are
`b ∈ (0, 1/2]` and `CA ≥ 0` with `b·m ≤ λ_{n+m}` and `|A_{n+m}| ≤ CA` for all
`m`, such that for `0 < ρ < 1`

* `ρ^{λ_{n+m}} ≤ (ρ^b)^m`, so every tail of the series is dominated by a
  geometric one;
* `Σ_m (n+m)^M |A_{n+m}| ρ^{λ_{n+m}}` converges for *every* `M : ℕ`, which is
  what lets any finite number of term-by-term differentiations be performed;
* `T_n` is the constant `A_n` off the origin, and
  `‖T_{n+m}(ξ)‖ ≤ 2|A_{n+m}| ‖ξ‖^{λ_{n+m}}`.

The engine is `LambdaLinearLowerBound`'s `λ_k ≥ (γ_n/(n+1))k` alone: it
converts `ρ^{λ_k}` into a geometric `q^k` with `q = ρ^{γ_n/(n+1)} < 1`.  The
constant lower bound `λ_k ≥ (p-1)/(np)` of (25) contributes nothing here,
being constant in `k`: it yields neither `λ_k → ∞` nor any decay.  This is the
paper's "we note that `lim λ_k = ∞`.  Therefore, we can perform any finite
number of term-by-term differentiations in formula (19)" (`paper.tex:387`) made
quantitative.

`b` and `CA` are produced existentially because only the listed inequalities
are ever used; no property of the particular witnesses `min(γ_n/(n+1), 1/2)`
and `(Σ_m (n+m)|A_{n+m}|²)^{1/2}` is needed downstream. -/
theorem Thm2TermGeometricSummability (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (A : ℤ → ℂ)
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    ∃ b CA : ℝ,
      0 < b
      ∧ b ≤ 1 / 2
      ∧ (∀ m : ℕ, b * (m : ℝ) ≤ LambdaCoef n (n + m) p)
      ∧ 0 ≤ CA
      ∧ (∀ m : ℕ, ‖A ((n : ℤ) + (m : ℤ))‖ ≤ CA)
      ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ m : ℕ,
          ρ ^ (LambdaCoef n (n + m) p) ≤ (ρ ^ b) ^ m)
      ∧ (∀ (M : ℕ) (ρ : ℝ), 0 < ρ → ρ < 1 →
          Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
            * ρ ^ (LambdaCoef n (n + m) p)))
      ∧ (∀ ξ : ℂ, ξ ≠ 0 → Thm2Term n p A n ξ = A (n : ℤ))
      ∧ (∀ (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
          ‖Thm2Term n p A (n + m) ξ‖
            ≤ 2 * ‖A ((n : ℤ) + (m : ℤ))‖ * ‖ξ‖ ^ LambdaCoef n (n + m) p)
      ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 →
          Summable (fun m : ℕ => 2 * ‖A ((n : ℤ) + (m : ℤ))‖
            * ρ ^ (LambdaCoef n (n + m) p))) := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
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
  obtain ⟨b, hb0, hbhalf, hbL⟩ : ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 2 ∧
      ∀ m : ℕ, b * (m : ℝ) ≤ LambdaCoef n (n + m) p := by
    refine ⟨min (GammaExp n p / ((n : ℝ) + 1)) (1 / 2), ?_, min_le_right _ _, fun m => ?_⟩
    · have h1 : (0 : ℝ) < GammaExp n p / ((n : ℝ) + 1) := by positivity
      exact lt_min h1 (by norm_num)
    · have hmin : min (GammaExp n p / ((n : ℝ) + 1)) (1 / 2)
          ≤ GammaExp n p / ((n : ℝ) + 1) := min_le_left _ _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hstep : min (GammaExp n p / ((n : ℝ) + 1)) (1 / 2) * (m : ℝ)
          ≤ GammaExp n p / ((n : ℝ) + 1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hmin hm0
      refine le_trans hstep ?_
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, Nat.add_zero, hlamn]
        norm_num
      · have hl := LambdaLinearLowerBound n p hn hp (n + m) (by omega)
        rw [hcast m] at hl
        have hmn : (m : ℝ) ≤ (n : ℝ) + (m : ℝ) := by linarith
        have h2 := mul_le_mul_of_nonneg_left hmn
          (by positivity : (0 : ℝ) ≤ GammaExp n p / ((n : ℝ) + 1))
        linarith
  obtain ⟨CA, hCA0, hCA⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ m : ℕ, ‖A ((n : ℤ) + (m : ℤ))‖ ≤ c := by
    refine ⟨Real.sqrt (∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2),
      Real.sqrt_nonneg _, fun m => ?_⟩
    have hEnn : (0 : ℝ) ≤ ∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 :=
      tsum_nonneg (fun j => by positivity)
    have h1 : ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2
        ≤ ∑' j : ℕ, ((n : ℝ) + (j : ℝ)) * ‖A ((n : ℤ) + (j : ℤ))‖ ^ 2 :=
      hsum.le_tsum m (fun j _ => by positivity)
    have h2 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    refine (Real.le_sqrt (norm_nonneg _) hEnn).mpr ?_
    nlinarith [sq_nonneg ‖A ((n : ℤ) + (m : ℤ))‖]
  have hqbd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ m : ℕ,
      ρ ^ (LambdaCoef n (n + m) p) ≤ (ρ ^ b) ^ m := by
    intro ρ h0 h1 m
    rw [← Real.rpow_natCast (ρ ^ b) m, ← Real.rpow_mul h0.le]
    exact Real.rpow_le_rpow_of_exponent_ge h0 h1.le (hbL m)
  -- ## Step 2: the summability engine
  have hgeo : ∀ (M : ℕ) (ρ : ℝ), 0 < ρ → ρ < 1 →
      Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
        * ρ ^ (LambdaCoef n (n + m) p)) := by
    intro M ρ hρ0 hρ1
    obtain ⟨q, hq0, hq1, hqρ⟩ : ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ m : ℕ,
        ρ ^ (LambdaCoef n (n + m) p) ≤ q ^ m := by
      refine ⟨ρ ^ b, Real.rpow_pos_of_pos hρ0 b, Real.rpow_lt_one hρ0.le hρ1 hb0, fun m => ?_⟩
      rw [← Real.rpow_natCast (ρ ^ b) m, ← Real.rpow_mul hρ0.le]
      exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (hbL m)
    have hqnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
    have h0 := summable_pow_mul_geometric_of_norm_lt_one M hqnorm
    have hg : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0.le hq1
    have hmaj : Summable (fun m : ℕ =>
        (((n : ℝ) + 1) ^ M * 2 ^ M * CA) * ((m : ℝ) ^ M * q ^ m)
          + (((n : ℝ) + 1) ^ M * 2 ^ M * CA) * q ^ m) := (h0.mul_left _).add (hg.mul_left _)
    have hsplit : ∀ x : ℝ, 0 ≤ x → (x + 1) ^ M ≤ 2 ^ M * (x ^ M + 1) := by
      intro x hx
      have h2 : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
      rcases le_or_gt x 1 with h | h
      · have h1 : (x + 1) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
        have h3 : (0 : ℝ) ≤ x ^ M := by positivity
        nlinarith
      · have h1 : (x + 1) ^ M ≤ (2 * x) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
        rw [mul_pow] at h1
        nlinarith
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmj : ((n : ℝ) + (m : ℝ)) ^ M
        ≤ ((n : ℝ) + 1) ^ M * 2 ^ M * ((m : ℝ) ^ M + 1) := by
      have e1 : ((n : ℝ) + (m : ℝ)) ^ M ≤ (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ M := by
        refine pow_le_pow_left₀ (by positivity) ?_ M
        nlinarith
      rw [mul_pow] at e1
      have e2 := hsplit (m : ℝ) hm0
      have e3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ M := by positivity
      calc ((n : ℝ) + (m : ℝ)) ^ M ≤ ((n : ℝ) + 1) ^ M * ((m : ℝ) + 1) ^ M := e1
        _ ≤ ((n : ℝ) + 1) ^ M * (2 ^ M * ((m : ℝ) ^ M + 1)) :=
            mul_le_mul_of_nonneg_left e2 e3
        _ = ((n : ℝ) + 1) ^ M * 2 ^ M * ((m : ℝ) ^ M + 1) := by ring
    have hqm : (0 : ℝ) ≤ q ^ m := by positivity
    have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
    calc ((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖ * ρ ^ (LambdaCoef n (n + m) p)
        ≤ (((n : ℝ) + 1) ^ M * 2 ^ M * ((m : ℝ) ^ M + 1)) * CA * q ^ m := by
          gcongr
          · exact hCA m
          · exact hqρ m
      _ = (((n : ℝ) + 1) ^ M * 2 ^ M * CA) * ((m : ℝ) ^ M * q ^ m)
            + (((n : ℝ) + 1) ^ M * 2 ^ M * CA) * q ^ m := by ring
  -- ## Step 1: the constant summand, and the pointwise bound on each summand
  have hTn : ∀ ξ : ℂ, ξ ≠ 0 → Thm2Term n p A n ξ = A (n : ℤ) := by
    intro ξ hξ
    have hpn : (ξ : ℂ) ^ n ≠ 0 := pow_ne_zero n hξ
    simp only [Thm2Term, hlamn, hepsn]
    rw [show (0 : ℝ) + (n : ℝ) - (n : ℝ) = 0 from by ring, Real.rpow_zero,
      zpow_neg, zpow_natCast]
    push_cast
    field_simp
    ring
  have hFbd : ∀ (k : ℕ) (ξ : ℂ),
      ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ ξ) ^ k‖
        ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
    intro k ξ
    have h1 : ‖A (k : ℤ) * ξ ^ k‖ = ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
      rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖ξ‖ k]
    have h2 : ‖((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ ξ) ^ k‖
        = |EpsCoef n k p| * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, ← Real.rpow_natCast ‖ξ‖ k]
      ring
    refine le_trans (norm_add_le _ _) ?_
    rw [h1, h2]
    exact le_of_eq (by ring)
  have hTnorm : ∀ (k : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ‖Thm2Term n p A k ξ‖
        ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ LambdaCoef n k p := by
    intro k ξ hξ
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hgn : ‖((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)‖
        = ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hr _)]
    have hpp : ‖ξ ^ (-(n : ℤ))‖ = ‖ξ‖ ^ (-(n : ℝ)) := by
      rw [norm_zpow, ← Real.rpow_intCast ‖ξ‖ (-(n : ℤ))]
      norm_num
    have hcomb : ‖ξ‖ ^ (k : ℝ) * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ))
          * ‖ξ‖ ^ (-(n : ℝ))
        = ‖ξ‖ ^ LambdaCoef n k p := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      ring
    have hmu : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hnn : (0 : ℝ) ≤ ‖ξ‖ ^ (-(n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖Thm2Term n p A k ξ‖
        = ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ ξ) ^ k‖
            * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) := by
          simp only [Thm2Term]
          rw [norm_mul, norm_mul, hgn, hpp]
      _ ≤ ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ))
            * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) := by
          gcongr
          exact hFbd k ξ
      _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖
            * (‖ξ‖ ^ (k : ℝ) * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ))
              * ‖ξ‖ ^ (-(n : ℝ))) := by ring
      _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ LambdaCoef n k p := by
          rw [hcomb]
  have hT2 : ∀ (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ‖Thm2Term n p A (n + m) ξ‖
        ≤ 2 * ‖A ((n : ℤ) + (m : ℤ))‖ * ‖ξ‖ ^ LambdaCoef n (n + m) p := by
    intro m ξ hξ
    have h := hTnorm (n + m) ξ hξ
    have hcastA : A (((n + m : ℕ)) : ℤ) = A ((n : ℤ) + (m : ℤ)) := by
      congr 1
    rw [hcastA] at h
    refine le_trans h ?_
    have he := hepsle m
    have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
    have hrr : (0 : ℝ) ≤ ‖ξ‖ ^ LambdaCoef n (n + m) p := Real.rpow_nonneg (norm_nonneg _) _
    gcongr
    linarith
  have hgeo0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      Summable (fun m : ℕ => 2 * ‖A ((n : ℤ) + (m : ℤ))‖
        * ρ ^ (LambdaCoef n (n + m) p)) := by
    intro ρ h0 h1
    have h := hgeo 0 ρ h0 h1
    simp only [pow_zero, one_mul] at h
    refine (h.mul_left 2).congr (fun m => ?_)
    ring
  exact ⟨b, CA, hb0, hbhalf, hbL, hCA0, hCA, hqbd, hgeo, hTn, hT2, hgeo0⟩
