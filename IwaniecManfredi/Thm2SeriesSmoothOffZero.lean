import IwaniecManfredi.Thm2TermWordDerivBound
import IwaniecManfredi.Thm2TermGeometricSummability
import IwaniecManfredi.LambdaEpsEstimates
set_option maxHeartbeats 1000000

/-- The series (19) is `C^∞` off the origin: for `n ≥ 1`, `1 < p < ∞` and
coefficients satisfying the energy hypothesis `Σ_m (n+m)|A_{n+m}|² < ∞`, the
pointwise sum `ξ ↦ Σ'_m T_{n+m}(ξ)` is `C^∞` on the punctured unit disc
`{ξ : ‖ξ‖ < 1} \ {0}`.

This is the paper's "we note that `lim λ_k = ∞`.  Therefore, we can perform any
finite number of term-by-term differentiations in formula (19)"
(`paper.tex:387`), carried out in full.  The two ingredients are already
nodes, and the content here is the induction that combines them: each summand
is `C^∞` off the origin and obeys the all-order word-derivative bound of
`Thm2TermWordDerivBound`, and that bound is summable in `m` at every order
against the geometric majorant of `Thm2TermGeometricSummability`.  So on a
small ball around any punctured point every order of the term-by-term
differentiated series converges uniformly, and a locally uniform limit of
`C^∞` functions whose derived series of every order converge locally
uniformly is itself `C^∞`.

The statement is about the series itself rather than about a function proved
equal to it, so it carries no hypothesis tying it to any particular `H`: a
consumer that has `H = Σ' T_{n+m}` off the origin transfers the conclusion by
congruence. -/
theorem Thm2SeriesSmoothOffZero (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (A : ℤ → ℂ)
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => ∑' m : ℕ, Thm2Term n p A (n + m) z)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
  -- the geometric summability engine supplies `hgeo`, the all-order majorant
  obtain ⟨b, CA, hb0, hbhalf, hbL, hCA0, hCA, hqbd, hgeo, hTn, hT2, hgeo0⟩ :=
    Thm2TermGeometricSummability n p hn hp A hsum
  -- `λ_{n+m} ≥ 0`, from (23) and (25) of the Remark
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  have hL0 : ∀ m : ℕ, 0 ≤ LambdaCoef n (n + m) p := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
    · have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
  -- estimate (11), the all-order word-derivative bound on a single summand,
  -- together with the smoothness of that summand off the origin: both are
  -- `Thm2TermWordDerivBound`, whose `E`-class calculus supplies them with no
  -- sector decomposition at all.
  obtain ⟨Dw, Vp, hDwnil, hDwcons, hVpv, Vpcons, Vpnonneg, Trepbd, hTcd⟩ :=
    Thm2TermWordDerivBound n p hn hp A
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the Wirtinger-free reconstruction of a real-linear map on `ℂ` from its two values
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ), ∀ (q : ℂ × ℂ) (v : ℂ),
      Θ q v = (v.re : ℂ) * q.1 + (v.im : ℂ) * q.2 := by
    refine ⟨(ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)
      + (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).comp
        (ContinuousLinearMap.snd ℝ ℂ ℂ), ?_⟩
    intro q v
    simp [ContinuousLinearMap.smulRightL_apply_apply, Complex.real_smul]
  have hdecompCLM : ∀ (L : ℂ →L[ℝ] ℂ) (v : ℂ),
      L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
    intro L v
    calc L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := by
          congr 1
          rw [Complex.real_smul, Complex.real_smul, mul_one]
          exact (Complex.re_add_im v).symm
      _ = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
          rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  refine contDiffOn_infty.mpr (fun N => ?_)
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  have hx1 : ‖x‖ < 1 := hx.1
  have hx0 : x ≠ 0 := by
    intro h
    exact hx.2 (by rw [h]; exact Set.mem_singleton 0)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hrad0 : (0 : ℝ) < min (‖x‖ / 2) ((1 - ‖x‖) / 2) := lt_min (by positivity) (by linarith)
  have hρ1 : (0 : ℝ) < ‖x‖ / 2 := by positivity
  have hρ2 : (0 : ℝ) < (1 + ‖x‖) / 2 := by linarith
  have hρ21 : (1 + ‖x‖) / 2 < 1 := by linarith
  have hsub : ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      z ≠ 0 ∧ ‖z‖ < (1 + ‖x‖) / 2 ∧ ‖x‖ / 2 ≤ ‖z‖ := by
    intro z hz
    have hdz : ‖z - x‖ < min (‖x‖ / 2) ((1 - ‖x‖) / 2) := by
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    have hd1 : ‖z - x‖ < ‖x‖ / 2 := lt_of_lt_of_le hdz (min_le_left _ _)
    have hd2 : ‖z - x‖ < (1 - ‖x‖) / 2 := lt_of_lt_of_le hdz (min_le_right _ _)
    have hA1 := norm_sub_norm_le z x
    have hA2 := norm_sub_norm_le x z
    rw [norm_sub_rev] at hA2
    have hzlow : ‖x‖ / 2 ≤ ‖z‖ := by linarith
    refine ⟨?_, by linarith, hzlow⟩
    intro hz0
    rw [hz0, norm_zero] at hzlow
    linarith
  obtain ⟨uu, huu⟩ : ∃ uu : ℕ → ℝ → ℕ → ℝ, ∀ (M : ℕ) (P : ℝ) (m : ℕ),
      uu M P m = 2 * (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M * P
            * ((‖x‖ / 2) ^ (-(M : ℝ)))
          * (((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
              * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) :=
    ⟨fun M P m => 2 * (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M * P
            * ((‖x‖ / 2) ^ (-(M : ℝ)))
          * (((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
              * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))), fun _ _ _ => rfl⟩
  have huusum : ∀ (M : ℕ) (P : ℝ), Summable (uu M P) := by
    intro M P
    have he : uu M P = fun m : ℕ =>
        (2 * (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M * P * ((‖x‖ / 2) ^ (-(M : ℝ))))
          * (((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
              * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := by
      funext m
      rw [huu]
    rw [he]
    exact (hgeo M ((1 + ‖x‖) / 2) hρ2 hρ21).mul_left _
  have huulin : ∀ (M : ℕ) (P c : ℝ) (m : ℕ), uu M (c * P) m = uu M P m * c := by
    intro M P c m
    rw [huu, huu]
    ring
  have huunn : ∀ (M : ℕ) (P : ℝ), 0 ≤ P → ∀ m : ℕ, 0 ≤ uu M P m := by
    intro M P hP m
    rw [huu]
    have h1 : (0 : ℝ) ≤ (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M := by positivity
    have h2 : (0 : ℝ) ≤ ((‖x‖ / 2) ^ (-(M : ℝ))) := Real.rpow_nonneg hρ1.le _
    have h3 : (0 : ℝ) ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) :=
      Real.rpow_nonneg hρ2.le _
    have h4 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
    have h5 : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ)) ^ M := by positivity
    positivity
  -- the uniform bound on the ball
  have hub : ∀ (w : List ℂ) (m : ℕ),
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      ‖Dw w (Thm2Term n p A (n + m)) z‖ ≤ uu w.length (Vp w) m := by
    intro w m z hz
    obtain ⟨hz0, hzup, hzlow⟩ := hsub z hz
    have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    refine le_trans (Trepbd w m z hz0) ?_
    have hX1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    -- step 1: the constant
    have hc1 : (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
        ≤ ((n : ℝ) + (m : ℝ)) * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) := by
      have h2 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
      have h1 : (w.length : ℝ) ≤ ((n : ℝ) + (m : ℝ)) * (w.length : ℝ) := by
        calc (w.length : ℝ) = 1 * (w.length : ℝ) := (one_mul _).symm
          _ ≤ ((n : ℝ) + (m : ℝ)) * (w.length : ℝ) := mul_le_mul_of_nonneg_right hX1 h2
      have h3 : ((n : ℝ) + (m : ℝ)) * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ)))
          = 2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)))
            + 2 * (((n : ℝ) + (m : ℝ)) * (w.length : ℝ)) := by ring
      rw [h3]
      linarith
    have hc1p : (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
          ^ (w.length)
        ≤ ((n : ℝ) + (m : ℝ)) ^ (w.length)
            * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hc1 _
    -- step 2: the power of `‖z‖`
    have hp2 : ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
        ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) * ((‖x‖ / 2) ^ (-(w.length : ℝ))) := by
      have hsplit : ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
          = ‖z‖ ^ (LambdaCoef n (n + m) p) * ‖z‖ ^ (-(w.length : ℝ)) := by
        rw [← Real.rpow_add hzr]
        ring_nf
      rw [hsplit]
      have hA : ‖z‖ ^ (LambdaCoef n (n + m) p)
          ≤ ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p) :=
        Real.rpow_le_rpow (norm_nonneg _) hzup.le (hL0 m)
      have hB : ‖z‖ ^ (-(w.length : ℝ)) ≤ (‖x‖ / 2) ^ (-(w.length : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hρ1 hzlow (by
          have : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
          linarith)
      exact mul_le_mul hA hB (Real.rpow_nonneg hzr.le _) (Real.rpow_nonneg hρ2.le _)
    rw [huu]
    have hVp : (0 : ℝ) ≤ Vp w := Vpnonneg w
    have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
    have hfac : (0 : ℝ) ≤ Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖) := by positivity
    have hpz : (0 : ℝ) ≤ ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hbig : (0 : ℝ) ≤ (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) := by
      positivity
    have hrp1 : (0 : ℝ) ≤ ((‖x‖ / 2) ^ (-(w.length : ℝ))) := Real.rpow_nonneg hρ1.le _
    have hrp2 : (0 : ℝ) ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) :=
      Real.rpow_nonneg hρ2.le _
    have hXn : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ)) ^ (w.length) := by positivity
    calc (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ))) ^ (w.length)
            * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
          * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
        = ((2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
              ^ (w.length))
            * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
              * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))) := by ring
      _ ≤ (((n : ℝ) + (m : ℝ)) ^ (w.length)
              * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length))
            * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
              * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))) := by
          refine mul_le_mul_of_nonneg_right hc1p ?_
          exact mul_nonneg hfac hpz
      _ ≤ (((n : ℝ) + (m : ℝ)) ^ (w.length)
              * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length))
            * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
              * ((((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))
                  * ((‖x‖ / 2) ^ (-(w.length : ℝ))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp2 hfac) ?_
          positivity
      _ = 2 * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) * Vp w
              * ((‖x‖ / 2) ^ (-(w.length : ℝ)))
            * (((n : ℝ) + (m : ℝ)) ^ (w.length) * ‖A ((n : ℤ) + (m : ℤ))‖
                * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := by ring
  have hssum : ∀ (w : List ℂ) (z : ℂ), z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)) →
      Summable (fun m : ℕ => Dw w (Thm2Term n p A (n + m)) z) := by
    intro w z hz
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hub w m z hz) (huusum w.length (Vp w)))
  have hfdbd : ∀ (w : List ℂ) (m : ℕ),
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      ‖fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z‖ ≤ uu (w.length + 1) (Vp w) m := by
    intro w m z hz
    refine ContinuousLinearMap.opNorm_le_bound _ (huunn _ _ (Vpnonneg w) m) (fun v => ?_)
    have he : fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z v
        = Dw (v :: w) (Thm2Term n p A (n + m)) z := by
      rw [hDwcons]
    rw [he]
    have h1 := hub (v :: w) m z hz
    have h2 : uu (v :: w).length (Vp (v :: w)) m = uu (w.length + 1) (Vp w) m * ‖v‖ := by
      rw [Vpcons, show (v :: w).length = w.length + 1 from by simp, huulin]
    rw [h2] at h1
    exact h1
  have hfdsum : ∀ (w : List ℂ) (z : ℂ), z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)) →
      Summable (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z) := by
    intro w z hz
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hfdbd w m z hz) (huusum (w.length + 1) (Vp w)))
  have hfd : ∀ (w : List ℂ) (z : ℂ), z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)) →
      HasFDerivAt (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y)
        (∑' m : ℕ, fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z) z := by
    intro w z hz
    exact hasFDerivAt_tsum_of_isPreconnected (huusum (w.length + 1) (Vp w))
      Metric.isOpen_ball (convex_ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))).isPreconnected
      (fun m y hy => ((hTcd w m y (hsub y hy).1).differentiableAt hone).hasFDerivAt)
      (fun m y hy => hfdbd w m y hy) (Metric.mem_ball_self hrad0)
      (hssum w x (Metric.mem_ball_self hrad0)) hz
  have hap : ∀ (w : List ℂ) (v z : ℂ),
      z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)) →
      fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z v
        = ∑' m : ℕ, Dw (v :: w) (Thm2Term n p A (n + m)) z := by
    intro w v z hz
    have hS : HasSum (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z)
        (fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z) := by
      rw [(hfd w z hz).fderiv]
      exact (hfdsum w z hz).hasSum
    have h2 := (ContinuousLinearMap.apply ℝ ℂ v).hasSum hS
    simp only [ContinuousLinearMap.apply_apply] at h2
    have h3 : (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z v)
        = fun m : ℕ => Dw (v :: w) (Thm2Term n p A (n + m)) z := by
      funext m
      rw [hDwcons]
    rw [h3] at h2
    exact (h2.tsum_eq).symm
  have hmain : ∀ (N : ℕ) (w : List ℂ),
      ContDiffOn ℝ (N : ℕ) (fun z : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) z)
        (Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))) := by
    intro N
    induction N with
    | zero =>
        intro w
        rw [Nat.cast_zero, contDiffOn_zero]
        refine continuousOn_tsum (fun m z hz => ?_) (huusum w.length (Vp w))
          (fun m z hz => hub w m z hz)
        exact ((hTcd w m z (hsub z hz).1).continuousAt).continuousWithinAt
    | succ N ih =>
        intro w
        rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = ((N : ℕ) : WithTop ℕ∞) + 1 from by
            push_cast; ring,
          contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
        refine ⟨?_, ?_, ?_⟩
        · intro z hz
          exact ((hfd w z hz).differentiableAt).differentiableWithinAt
        · intro h
          exact absurd h (by simp)
        · refine (Θ.contDiff.comp_contDiffOn
            ((ih (1 :: w)).prodMk (ih (Complex.I :: w)))).congr ?_
          intro z hz
          refine ContinuousLinearMap.ext (fun v => ?_)
          simp only [Function.comp_apply]
          rw [hdecompCLM
              (fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z) v,
            hap w 1 z hz, hap w Complex.I z hz]
          exact (hΘ (∑' m : ℕ, Dw (1 :: w) (Thm2Term n p A (n + m)) z,
            ∑' m : ℕ, Dw (Complex.I :: w) (Thm2Term n p A (n + m)) z) v).symm
  refine ⟨Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)), Metric.isOpen_ball,
    Metric.mem_ball_self hrad0, ?_⟩
  refine ContDiffOn.mono ?_ Set.inter_subset_right
  have he : (fun z : ℂ => ∑' m : ℕ, Thm2Term n p A (n + m) z)
      = fun z : ℂ => ∑' m : ℕ, Dw [] (Thm2Term n p A (n + m)) z := by
    funext z
    exact tsum_congr (fun m => by rw [hDwnil])
  rw [he]
  exact hmain N []
