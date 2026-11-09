import IwaniecManfredi.Thm2TermSolvesEq18
import IwaniecManfredi.LambdaLinearLowerBound
import IwaniecManfredi.GammaRatioMinAtOne
import IwaniecManfredi.FourierCoefOfH
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.WirtingerPolarForm
import IwaniecManfredi.Thm2TermWirtingerDerivs
import IwaniecManfredi.Thm2TermGeometricSummability
import IwaniecManfredi.Thm2TermWordDerivBound
import IwaniecManfredi.PolarSeparatedSumEnergy
import IwaniecManfredi.Thm2TermDerivBound
import IwaniecManfredi.Thm2SeriesSmoothOffZero
import IwaniecManfredi.Thm2TermPolarWirtingerDerivs
import IwaniecManfredi.Thm2SeriesCircleFourierCoef
import IwaniecManfredi.Thm2SeriesContinuousOnDisc

set_option maxHeartbeats 1000000


open MeasureTheory

/-- The `W^{1,2}(B)` convergence of the series (19), which both halves of
Theorem 2 assert and which the circlewise `L²` statement of the Fourier
expansion does not supply.  Given coefficients with `Σ k|A_k|² < ∞` obeying the
compatibility relation (39), the series converges in `W^{1,2}(B)` to a function
`H` continuous on `B`, smooth off the origin, whose Fourier coefficients are
exactly `A_k r^{λ_k}` for `|k| ≥ n` and vanish for `|k| < n`.  The estimate is
the energy computation run on tails: the `L²(B)` norms of the `k`-th summand
and of its two Wirtinger derivatives are all `O(k|A_k|²)`, and distinct
summands are orthogonal because their angular frequencies `k - n` and `-k - n`
are pairwise distinct. -/
theorem Thm2SeriesW12Convergence (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (A : ℤ → ℂ)
    (hcomp : ∀ k : ℤ, (n : ℤ) ≤ k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k))
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    ∃ H : ℂ → ℂ,
      ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) H ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) ∧
      MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H ∧
      IntegrableOn (fun ξ : ℂ => ‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)
        {ξ : ℂ | ‖ξ‖ < 1} volume ∧
      (∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)) ∧
      (∀ k : ℤ, |k| < (n : ℤ) → ∀ r ∈ Set.Ioo (0 : ℝ) 1, FourierCoefOfH n H k r = 0) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
              ‖H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k ξ‖ ^ 2)
          + (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
              ‖DZ H ξ
                - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2)
          + (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
              ‖DZbar H ξ
                - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2))
        Filter.atTop (nhds 0) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  have hcast : ∀ m : ℕ, (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := by
    intro m; push_cast; ring
  -- `λ_{n+m} ≥ 0` and `|ε_{n+m}| ≤ 1`
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
  -- ## Steps 1 and 2: the summability engine.  `b` is an opaque positive linear rate
  -- for `λ`, `CA` an opaque bound on `|A_k|`, and together they turn every tail of
  -- the series into a geometric one at every polynomial weight.
  obtain ⟨b, CA, hb0, hbhalf, hbL, hCA0, hCA, hqbd, hgeo, hTn, hT2, hgeo0⟩ :=
    Thm2TermGeometricSummability n p hn hp A hsum
  -- ## The construction: `H` is the pointwise sum of the series off the origin,
  -- completed at the origin by the value `A_n` of the constant summand `T_n`.
  set H : ℂ → ℂ := fun ξ => if ξ = 0 then A (n : ℤ) else ∑' m : ℕ, Thm2Term n p A (n + m) ξ
    with hHdef
  have hHval : ∀ ξ : ℂ, ξ ≠ 0 → H ξ = ∑' m : ℕ, Thm2Term n p A (n + m) ξ := by
    intro ξ hξ
    simp only [hHdef]
    rw [if_neg hξ]
  have hTca : ∀ (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (Thm2Term n p A (n + m)) ξ :=
    fun m => (Thm2TermSolvesEq18 n p hn hp (n + m) (by omega) A).1
  -- ## Step 4: `H` is `C^∞` off the origin.  The series is differentiated word by
  -- word: every word derivative of a summand stays inside the class spanned by the
  -- monomials `E s j l ξ = |ξ|^s ξ^j conj(ξ)^l`, where one differentiation drops
  -- the total exponent `s + j + l` by one and multiplies the coefficient by at most
  -- `|s|/2 + |j| + |l|`.  That is the only estimate the induction on the order
  -- consumes, and it is summable in `m` by `hgeo` at every order.  This is
  -- conjunct (b); it is proved here, where the local context is still small.
  have hContB : ContDiffOn ℝ (⊤ : ℕ∞) H ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    have hcongrH : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℂ => ∑' m : ℕ, Thm2Term n p A (n + m) z)
        ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) → ContDiffOn ℝ (⊤ : ℕ∞) H
        ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
      intro h
      refine h.congr ?_
      intro z hz
      refine hHval z ?_
      intro h0
      exact hz.2 (by rw [h0]; exact Set.mem_singleton 0)
    refine hcongrH ?_
    -- the series is `C^∞` off the origin: `Thm2SeriesSmoothOffZero`
    exact Thm2SeriesSmoothOffZero n p hn hp A hsum
  have hnormsum : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      Summable (fun m : ℕ => ‖Thm2Term n p A (n + m) ξ‖) := by
    intro ξ hξ hξ1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hT2 m ξ hξ)
      (hgeo0 ‖ξ‖ hr hξ1)
  -- ## Steps 3 and 4: `H` is continuous on the whole disc, the origin included.
  -- Off the origin this is local uniform convergence on annuli; at the origin the
  -- tail is dominated by `‖ξ‖^b` and the value `A_n` of the constant summand is
  -- what the completion assigns.  This is conjunct (a).
  have hHcontOn : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1} := by
    rw [hHdef]
    exact Thm2SeriesContinuousOnDisc n p hn hp A hsum
  -- `√(p-1) ≥ 0`, which several later `linarith` calls read from the context
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
  -- ## Step 6 preparation: the uniform pointwise bound on the two Wirtinger
  -- derivatives of each summand is `Thm2TermDerivBound`
  have hDbd := fun (m : ℕ) (ξ : ℂ) (hξ : ξ ≠ 0) => Thm2TermDerivBound n p hn hp A m ξ hξ
  -- ## Step 9 preparation: the real differential of each summand and of `H`
  have hdecomp : ∀ (f : ℂ → ℂ) (z v : ℂ),
      fderiv ℝ f z v = DZ f z * v + DZbar f z * (starRingEnd ℂ v) := by
    intro f z v
    obtain ⟨x, y, hvv⟩ : ∃ x y : ℝ, v = (x : ℂ) + (y : ℂ) * Complex.I :=
      ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
    subst hvv
    have hsm : ((x : ℂ) + (y : ℂ) * Complex.I) = x • (1 : ℂ) + y • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
    have hlin : fderiv ℝ f z ((x : ℂ) + (y : ℂ) * Complex.I)
        = (x : ℂ) * fderiv ℝ f z 1 + (y : ℂ) * fderiv ℝ f z Complex.I := by
      rw [hsm, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hconj : (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)
        = (x : ℂ) - (y : ℂ) * Complex.I := by
      simp [sub_eq_add_neg]
    rw [hlin, hconj, DZ, DZbar]
    linear_combination ((y : ℂ) * fderiv ℝ f z Complex.I) * Complex.I_sq
  have hfdbd : ∀ (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ‖fderiv ℝ (Thm2Term n p A (n + m)) ξ‖
        ≤ 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) := by
    intro m ξ hξ
    obtain ⟨h1, h2⟩ := hDbd m ξ hξ
    have hM0 : (0 : ℝ) ≤ 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ))
        * ‖A ((n : ℤ) + (m : ℤ))‖ * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) := by
      have hpw : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
      have hnm : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ 4 + Real.sqrt (p - 1) := by linarith
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun v => ?_)
    rw [hdecomp]
    have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
    calc ‖DZ (Thm2Term n p A (n + m)) ξ * v
            + DZbar (Thm2Term n p A (n + m)) ξ * starRingEnd ℂ v‖
        ≤ ‖DZ (Thm2Term n p A (n + m)) ξ * v‖
            + ‖DZbar (Thm2Term n p A (n + m)) ξ * starRingEnd ℂ v‖ := norm_add_le _ _
      _ = ‖DZ (Thm2Term n p A (n + m)) ξ‖ * ‖v‖
            + ‖DZbar (Thm2Term n p A (n + m)) ξ‖ * ‖v‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) * ‖v‖
            + ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) * ‖v‖ := by
          have e1 := mul_le_mul_of_nonneg_right h1 hv0
          have e2 := mul_le_mul_of_nonneg_right h2 hv0
          linarith
      _ = 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) * ‖v‖ := by ring
  have hgeo1 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
        * ρ ^ (LambdaCoef n (n + m) p)) := by
    intro ρ h0 h1
    have h := hgeo 1 ρ h0 h1
    simpa using h
  have hTfderiv : ∀ (m : ℕ) (ζ : ℂ), ζ ≠ 0 →
      HasFDerivAt (Thm2Term n p A (n + m)) (fderiv ℝ (Thm2Term n p A (n + m)) ζ) ζ :=
    fun m ζ hζ => ((hTca m ζ hζ).differentiableAt (by simp)).hasFDerivAt
  have hballpos : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 →
      (0 : ℝ) < min (‖x‖ / 2) ((1 - ‖x‖) / 2) := by
    intro x hx hx1
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact lt_min (by positivity) (by linarith)
  have hsub : ∀ x : ℂ, x ≠ 0 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
        z ≠ 0 ∧ ‖z‖ < (1 + ‖x‖) / 2 ∧ ‖x‖ / 2 ≤ ‖z‖ := by
    intro x hx z hz
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
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
  have hupper : ∀ x : ℂ, x ≠ 0 → ∀ (m : ℕ),
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
        ‖fderiv ℝ (Thm2Term n p A (n + m)) z‖
          ≤ (2 * (4 + Real.sqrt (p - 1)) / (‖x‖ / 2))
            * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
                * ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) := by
    intro x hx m z hz
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨hz0, hzup, hzlow⟩ := hsub x hx z hz
    have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    refine le_trans (hfdbd m z hz0) ?_
    have hpow : ‖z‖ ^ (LambdaCoef n (n + m) p - 1)
        ≤ ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p) / (‖x‖ / 2) := by
      have hsplit : ‖z‖ ^ (LambdaCoef n (n + m) p - 1)
          = ‖z‖ ^ LambdaCoef n (n + m) p / ‖z‖ := by
        rw [Real.rpow_sub hzr, Real.rpow_one]
      rw [hsplit]
      have hnum : ‖z‖ ^ LambdaCoef n (n + m) p
          ≤ ((1 + ‖x‖) / 2) ^ LambdaCoef n (n + m) p :=
        Real.rpow_le_rpow (norm_nonneg _) hzup.le (hL0 m)
      have hden : (0 : ℝ) < ‖x‖ / 2 := by positivity
      have hnum0 : (0 : ℝ) ≤ ((1 + ‖x‖) / 2) ^ LambdaCoef n (n + m) p :=
        Real.rpow_nonneg (by linarith) _
      calc ‖z‖ ^ LambdaCoef n (n + m) p / ‖z‖
          ≤ ((1 + ‖x‖) / 2) ^ LambdaCoef n (n + m) p / ‖z‖ :=
            div_le_div_of_nonneg_right hnum hzr.le
        _ ≤ ((1 + ‖x‖) / 2) ^ LambdaCoef n (n + m) p / (‖x‖ / 2) :=
            div_le_div_of_nonneg_left hnum0 hden hzlow
    have hc0 : (0 : ℝ) ≤ 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ))
        * ‖A ((n : ℤ) + (m : ℤ))‖) := by
      have h4 : (0 : ℝ) ≤ 4 + Real.sqrt (p - 1) := by
        have := Real.sqrt_nonneg (p - 1)
        linarith
      have hnm : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
      have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
      positivity
    calc 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖z‖ ^ (LambdaCoef n (n + m) p - 1))
        = (2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖))
            * ‖z‖ ^ (LambdaCoef n (n + m) p - 1) := by ring
      _ ≤ (2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖))
            * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p) / (‖x‖ / 2)) :=
          mul_le_mul_of_nonneg_left hpow hc0
      _ = (2 * (4 + Real.sqrt (p - 1)) / (‖x‖ / 2))
            * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
                * ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) := by
          field_simp
  have hu : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 →
      Summable (fun m : ℕ => (2 * (4 + Real.sqrt (p - 1)) / (‖x‖ / 2))
        * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := by
    intro x hx hx1
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact (hgeo1 ((1 + ‖x‖) / 2) (by positivity) (by linarith)).mul_left _
  have hHfd : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 →
      HasFDerivAt H (∑' m : ℕ, fderiv ℝ (Thm2Term n p A (n + m)) x) x := by
    intro x hx hx1
    have hrad0 := hballpos x hx hx1
    have hG := hasFDerivAt_tsum_of_isPreconnected (hu x hx hx1) Metric.isOpen_ball
      (convex_ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))).isPreconnected
      (fun m z hz => hTfderiv m z (hsub x hx z hz).1) (hupper x hx)
      (Metric.mem_ball_self hrad0) (Summable.of_norm (hnormsum x hx hx1))
      (Metric.mem_ball_self hrad0)
    refine hG.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrad0)) (fun z hz => ?_)
    exact hHval z (hsub x hx z hz).1
  have hfdcont : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 → ContinuousAt (fderiv ℝ H) x := by
    intro x hx hx1
    have hrad0 := hballpos x hx hx1
    have hEq : Set.EqOn (fderiv ℝ H)
        (fun z : ℂ => ∑' m : ℕ, fderiv ℝ (Thm2Term n p A (n + m)) z)
        (Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))) := by
      intro z hz
      obtain ⟨hz0, hzup, hzlow⟩ := hsub x hx z hz
      have hz1 : ‖z‖ < 1 := by
        have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have : (1 + ‖x‖) / 2 < 1 := by linarith
        linarith
      exact (hHfd z hz0 hz1).fderiv
    have hcontT : ∀ m : ℕ, ContinuousOn (fun z : ℂ => fderiv ℝ (Thm2Term n p A (n + m)) z)
        (Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))) := by
      intro m z hz
      exact (((hTca m z (hsub x hx z hz).1).continuousAt_fderiv
        (by simp)).continuousWithinAt)
    have htc : ContinuousOn (fun z : ℂ => ∑' m : ℕ, fderiv ℝ (Thm2Term n p A (n + m)) z)
        (Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))) :=
      continuousOn_tsum hcontT (hu x hx hx1) (hupper x hx)
    exact (htc.congr hEq).continuousAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrad0))
  have hfd0 : ∀ x : ℂ, x ≠ 0 → fderiv ℝ (Thm2Term n p A (n + 0)) x = 0 := by
    intro x hx
    have heq : (Thm2Term n p A (n + 0)) =ᶠ[nhds x] (fun _ : ℂ => A (n : ℤ)) := by
      refine Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hx) (fun z hz => ?_)
      rw [Nat.add_zero]
      exact hTn z hz
    rw [heq.fderiv_eq]
    simp
  have hpwbd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (m : ℕ) (x : ℂ), x ≠ 0 → ‖x‖ ≤ ρ →
      ‖fderiv ℝ (Thm2Term n p A (n + m)) x‖
        ≤ (2 * (4 + Real.sqrt (p - 1)) / ρ ^ b * ‖x‖ ^ (b - 1))
            * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
                * ρ ^ (LambdaCoef n (n + m) p)) := by
    intro ρ hρ0 hρ1 m x hx hxρ
    have hxr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
    have hx1 : (0 : ℝ) ≤ ‖x‖ ^ (b - 1) := Real.rpow_nonneg (norm_nonneg _) _
    have hρl : (0 : ℝ) ≤ ρ ^ (LambdaCoef n (n + m) p) := Real.rpow_nonneg hρ0.le _
    have hρb : (0 : ℝ) < ρ ^ b := Real.rpow_pos_of_pos hρ0 b
    have h4 : (0 : ℝ) ≤ 4 + Real.sqrt (p - 1) := by linarith
    have hnm : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, hfd0 x hx, norm_zero]
      have : (0 : ℝ) ≤ 2 * (4 + Real.sqrt (p - 1)) / ρ ^ b * ‖x‖ ^ (b - 1) := by positivity
      have h2 : (0 : ℝ) ≤ ((n : ℝ) + ((0 : ℕ) : ℝ)) * ‖A ((n : ℤ) + ((0 : ℕ) : ℤ))‖
          * ρ ^ (LambdaCoef n (n + 0) p) := by
        have hA0' : (0 : ℝ) ≤ ‖A ((n : ℤ) + ((0 : ℕ) : ℤ))‖ := norm_nonneg _
        have hρl' : (0 : ℝ) ≤ ρ ^ (LambdaCoef n (n + 0) p) := Real.rpow_nonneg hρ0.le _
        have hnm' : (0 : ℝ) ≤ (n : ℝ) + ((0 : ℕ) : ℝ) := by positivity
        positivity
      exact mul_nonneg this h2
    · refine le_trans (hfdbd m x hx) ?_
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hlb : b ≤ LambdaCoef n (n + m) p := by
        have h := hbL m
        nlinarith
      have hstep : ‖x‖ ^ (LambdaCoef n (n + m) p - 1)
          ≤ ‖x‖ ^ (b - 1) * (ρ ^ (LambdaCoef n (n + m) p) / ρ ^ b) := by
        have e1 : ‖x‖ ^ (LambdaCoef n (n + m) p - 1)
            = ‖x‖ ^ (b - 1) * ‖x‖ ^ (LambdaCoef n (n + m) p - b) := by
          rw [← Real.rpow_add hxr]
          congr 1
          ring
        have e2 : ‖x‖ ^ (LambdaCoef n (n + m) p - b) ≤ ρ ^ (LambdaCoef n (n + m) p - b) :=
          Real.rpow_le_rpow (norm_nonneg _) hxρ (by linarith)
        have e3 : ρ ^ (LambdaCoef n (n + m) p - b)
            = ρ ^ (LambdaCoef n (n + m) p) / ρ ^ b := Real.rpow_sub hρ0 _ _
        rw [e1, ← e3]
        exact mul_le_mul_of_nonneg_left e2 hx1
      have hc0 : (0 : ℝ) ≤ 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ))
          * ‖A ((n : ℤ) + (m : ℤ))‖) := by positivity
      calc 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
              * ‖x‖ ^ (LambdaCoef n (n + m) p - 1))
          = (2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖))
              * ‖x‖ ^ (LambdaCoef n (n + m) p - 1) := by ring
        _ ≤ (2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖))
              * (‖x‖ ^ (b - 1) * (ρ ^ (LambdaCoef n (n + m) p) / ρ ^ b)) :=
            mul_le_mul_of_nonneg_left hstep hc0
        _ = (2 * (4 + Real.sqrt (p - 1)) / ρ ^ b * ‖x‖ ^ (b - 1))
              * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
                  * ρ ^ (LambdaCoef n (n + m) p)) := by
            field_simp
  have hHgrad : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ ρ →
      ‖fderiv ℝ H x‖
        ≤ (2 * (4 + Real.sqrt (p - 1)) / ρ ^ b
              * (∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
                  * ρ ^ (LambdaCoef n (n + m) p)))
          * ‖x‖ ^ (b - 1) := by
    intro ρ hρ0 hρ1 x hx hxρ
    have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hxρ hρ1
    have hbd := fun m => hpwbd ρ hρ0 hρ1 m x hx hxρ
    have hsum := (hgeo1 ρ hρ0 hρ1).mul_left
      (2 * (4 + Real.sqrt (p - 1)) / ρ ^ b * ‖x‖ ^ (b - 1))
    have hns : Summable (fun m : ℕ => ‖fderiv ℝ (Thm2Term n p A (n + m)) x‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbd hsum
    rw [(hHfd x hx hx1).fderiv]
    refine le_trans (norm_tsum_le_tsum_norm hns) ?_
    refine le_trans (Summable.tsum_le_tsum hbd hns hsum) ?_
    rw [tsum_mul_left]
    exact le_of_eq (by ring)
  -- ## Step 9: `H` is `C¹` off the origin, and locally `L¹`/`L²` with its gradient
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hBmin : IsOpen ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    rw [Set.sdiff_eq]
    exact hBopen.inter isOpen_compl_singleton
  have hmem : ∀ z ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}), z ≠ 0 ∧ ‖z‖ < 1 := by
    intro z hz
    refine ⟨?_, hz.1⟩
    intro h
    exact hz.2 (by rw [h]; exact Set.mem_singleton 0)
  have hC1 : ContDiffOn ℝ (1 : ℕ) H ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    rw [show ((1 : ℕ) : WithTop ℕ∞) = 0 + 1 from by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen hBmin]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact ((hHfd z (hmem z hz).1 (hmem z hz).2).differentiableAt).differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · rw [contDiffOn_zero]
      intro z hz
      exact (hfdcont z (hmem z hz).1 (hmem z hz).2).continuousWithinAt
  have hPW : ∀ (j : Fin 2) (z : ℂ), PartialWord [j] H z
      = fderiv ℝ H z (if j = 0 then 1 else Complex.I) := by
    intro j z
    rfl
  have hPWbdfd : ∀ (j : Fin 2) (z : ℂ), ‖PartialWord [j] H z‖ ≤ ‖fderiv ℝ H z‖ := by
    intro j z
    rw [hPW j z]
    have hv : ‖(if j = 0 then (1 : ℂ) else Complex.I)‖ = 1 := by
      by_cases hj : j = 0
      · rw [if_pos hj, norm_one]
      · rw [if_neg hj, Complex.norm_I]
    have h := (fderiv ℝ H z).le_opNorm (if j = 0 then (1 : ℂ) else Complex.I)
    rw [hv, mul_one] at h
    exact h
  have hPWmeas : ∀ j : Fin 2, Measurable (PartialWord [j] H) := by
    intro j
    have h : Measurable (fun z : ℂ => fderiv ℝ H z (if j = 0 then 1 else Complex.I)) :=
      measurable_fderiv_apply_const ℝ H (if j = 0 then 1 else Complex.I)
    exact (funext (hPW j) : PartialWord [j] H = _) ▸ h
  have hKrad : ∀ Kc : Set ℂ, Kc ⊆ {ξ : ℂ | ‖ξ‖ < 1} → IsCompact Kc →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ z ∈ Kc, ‖z‖ ≤ ρ := by
    intro Kc hKc hKcc
    rcases Kc.eq_empty_or_nonempty with h | h
    · exact ⟨1 / 2, by norm_num, by norm_num, by simp [h]⟩
    · obtain ⟨z₀, hz₀, hmax⟩ := hKcc.exists_isMaxOn h continuous_norm.continuousOn
      have hz₀1 : ‖z₀‖ < 1 := hKc hz₀
      refine ⟨(1 + ‖z₀‖) / 2, by positivity, by linarith, fun z hz => ?_⟩
      have h1 : ‖z‖ ≤ ‖z₀‖ := hmax hz
      linarith
  have hmem2 : ∀ (μ : MeasureTheory.Measure ℂ) (f : ℂ → ℂ),
      MeasureTheory.AEStronglyMeasurable f μ →
      MeasureTheory.Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) μ →
      MeasureTheory.MemLp f 2 μ := by
    intro μ f hf hint
    have hdiv : (2 : ENNReal) / (2 : ENNReal) = 1 :=
      ENNReal.div_self (by norm_num) (by norm_num)
    have hstep : MeasureTheory.MemLp (fun x => ‖f x‖ ^ ((2 : ENNReal)).toReal)
        ((2 : ENNReal) / (2 : ENNReal)) μ := by
      rw [hdiv, show ((2 : ENNReal)).toReal = (2 : ℝ) from by norm_num]
      exact MeasureTheory.memLp_one_iff_integrable.mpr hint
    exact (MeasureTheory.memLp_norm_rpow_iff hf (by norm_num) (by norm_num)).mp hstep
  have hpow1int : MeasureTheory.IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(1 : ℝ)))
      (Metric.ball (0 : ℂ) 1) MeasureTheory.volume := by
    have h := PowerIntegrableNearZero 1 one_pos le_rfl 1 one_pos 1 le_rfl (by norm_num)
    rw [show ((1 : ℝ) - 2) * 1 = -(1 : ℝ) from by norm_num] at h
    exact h
  have hpow2int : MeasureTheory.IntegrableOn (fun z : ℂ => ‖z‖ ^ (2 * b - 2))
      (Metric.ball (0 : ℂ) 1) MeasureTheory.volume := by
    have hq2 : (1 : ℝ) < 2 / (2 - 2 * b) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have h := PowerIntegrableNearZero (2 * b) (by linarith) (by linarith) 1 one_pos 1 le_rfl hq2
    rw [show (2 * b - 2) * 1 = 2 * b - 2 from by ring] at h
    exact h
  have hballeq : Metric.ball (0 : ℂ) 1 = {ξ : ℂ | ‖ξ‖ < 1} := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have hS0 : ({0} : Set ℂ) ⊆ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    simp [hz]
  have hSfin : ∀ Kc ⊆ {ξ : ℂ | ‖ξ‖ < 1}, IsCompact Kc →
      (({0} : Set ℂ) ∩ Kc).Finite := fun Kc _ _ => (Set.finite_singleton 0).inter_of_left _
  have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    simp
  have hHloc : ∀ s : ENNReal, MemLpLocOn s {ξ : ℂ | ‖ξ‖ < 1} H := by
    intro s Kc hKc hKcc
    rw [MeasureTheory.memLp_indicator_iff_restrict hKcc.measurableSet]
    have hfm : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Kc) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact hKcc.measure_lt_top
    obtain ⟨C, hC⟩ := hKcc.exists_bound_of_continuousOn (hHcontOn.mono hKc)
    refine MeasureTheory.MemLp.of_bound
      ((hHcontOn.mono hKc).aestronglyMeasurable hKcc.measurableSet) C ?_
    refine (MeasureTheory.ae_restrict_iff' hKcc.measurableSet).mpr ?_
    exact Filter.Eventually.of_forall (fun z hz => hC z hz)
  have hvbd : ∀ Kc : Set ℂ, Kc ⊆ {ξ : ℂ | ‖ξ‖ < 1} → IsCompact Kc → ∀ j : Fin 2,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kc, z ≠ 0 → ‖PartialWord [j] H z‖ ≤ C * ‖z‖ ^ (b - 1) := by
    intro Kc hKc hKcc j
    obtain ⟨ρ, hρ0, hρ1, hρK⟩ := hKrad Kc hKc hKcc
    have hts : (0 : ℝ) ≤ ∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
        * ρ ^ (LambdaCoef n (n + m) p) := by
      refine tsum_nonneg (fun m => ?_)
      have h1 : (0 : ℝ) ≤ ρ ^ (LambdaCoef n (n + m) p) := Real.rpow_nonneg hρ0.le _
      have h2 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
      have h3 : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
      positivity
    refine ⟨2 * (4 + Real.sqrt (p - 1)) / ρ ^ b
      * (∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
          * ρ ^ (LambdaCoef n (n + m) p)), ?_, fun z hz hz0 => ?_⟩
    · have h4 : (0 : ℝ) ≤ 4 + Real.sqrt (p - 1) := by
        have := Real.sqrt_nonneg (p - 1)
        linarith
      have hρb : (0 : ℝ) < ρ ^ b := Real.rpow_pos_of_pos hρ0 b
      positivity
    · exact le_trans (hPWbdfd j z) (hHgrad ρ hρ0 hρ1 z hz0 (hρK z hz))
  have hPWloc1 : ∀ j : Fin 2, MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} (PartialWord [j] H) := by
    intro j Kc hKc hKcc
    obtain ⟨C, hC0, hCbd⟩ := hvbd Kc hKc hKcc j
    rw [MeasureTheory.memLp_one_iff_integrable]
    have hmaj : MeasureTheory.Integrable
        ((Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => C * ‖z‖ ^ (-(1 : ℝ))))
        MeasureTheory.volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_ball).mpr (hpow1int.const_mul _)
    refine MeasureTheory.Integrable.mono' hmaj
      ((hPWmeas j).indicator hKcc.measurableSet).aestronglyMeasurable ?_
    filter_upwards [hne0] with z hz
    by_cases hzK : z ∈ Kc
    · have hzB : z ∈ Metric.ball (0 : ℂ) 1 := by
        rw [hballeq]
        exact hKc hzK
      have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hz1 : ‖z‖ < 1 := by
        rw [hballeq] at hzB
        exact hzB
      rw [Set.indicator_of_mem hzK, Set.indicator_of_mem hzB]
      refine le_trans (hCbd z hzK hz) ?_
      have hpow : ‖z‖ ^ (b - 1) ≤ ‖z‖ ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hzr hz1.le (by linarith)
      exact mul_le_mul_of_nonneg_left hpow hC0
    · rw [Set.indicator_of_notMem hzK, norm_zero]
      by_cases hzB : z ∈ Metric.ball (0 : ℂ) 1
      · rw [Set.indicator_of_mem hzB]
        have : (0 : ℝ) ≤ ‖z‖ ^ (-(1 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        positivity
      · rw [Set.indicator_of_notMem hzB]
  have hPWloc2 : ∀ j : Fin 2, MemLpLocOn 2 {ξ : ℂ | ‖ξ‖ < 1} (PartialWord [j] H) := by
    intro j Kc hKc hKcc
    obtain ⟨C, hC0, hCbd⟩ := hvbd Kc hKc hKcc j
    refine hmem2 _ _ ((hPWmeas j).indicator hKcc.measurableSet).aestronglyMeasurable ?_
    have hmaj : MeasureTheory.Integrable
        ((Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => C ^ 2 * ‖z‖ ^ (2 * b - 2)))
        MeasureTheory.volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_ball).mpr (hpow2int.const_mul _)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact ((((hPWmeas j).indicator hKcc.measurableSet).norm).pow
        measurable_const).aestronglyMeasurable
    · filter_upwards [hne0] with z hz
      have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz
      by_cases hzK : z ∈ Kc
      · have hzB : z ∈ Metric.ball (0 : ℂ) 1 := by
          rw [hballeq]
          exact hKc hzK
        rw [Set.indicator_of_mem hzK, Set.indicator_of_mem hzB]
        have hb1 := hCbd z hzK hz
        have hrp : (0 : ℝ) ≤ ‖z‖ ^ (b - 1) := Real.rpow_nonneg (norm_nonneg _) _
        have hstep : ‖PartialWord [j] H z‖ ^ (2 : ℝ) ≤ (C * ‖z‖ ^ (b - 1)) ^ (2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hb1 (by norm_num)
        have hC2 : C ^ (2 : ℝ) = C ^ 2 := by
          rw [← Real.rpow_natCast C 2]
          norm_num
        have hexp : (C * ‖z‖ ^ (b - 1)) ^ (2 : ℝ) = C ^ 2 * ‖z‖ ^ (2 * b - 2) := by
          rw [Real.mul_rpow hC0 hrp, hC2, ← Real.rpow_mul (norm_nonneg _),
            show (b - 1) * 2 = 2 * b - 2 from by ring]
        have hnn : (0 : ℝ) ≤ ‖PartialWord [j] H z‖ ^ (2 : ℝ) :=
          Real.rpow_nonneg (norm_nonneg _) _
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, ← hexp]
        exact hstep
      · rw [Set.indicator_of_notMem hzK]
        simp only [norm_zero]
        rw [Real.zero_rpow (by norm_num), Real.norm_eq_abs, abs_zero]
        by_cases hzB : z ∈ Metric.ball (0 : ℂ) 1
        · rw [Set.indicator_of_mem hzB]
          have : (0 : ℝ) ≤ ‖z‖ ^ (2 * b - 2) := Real.rpow_nonneg (norm_nonneg _) _
          positivity
        · rw [Set.indicator_of_notMem hzB]
  have hcbsub : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    show ‖z‖ < 1
    linarith
  have hweak : ∀ j : Fin 2,
      IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} j H (PartialWord [j] H) := by
    intro j
    obtain ⟨MH, hMH⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hHcontOn.mono hcbsub)
    refine WeakPartialAcrossPoint {ξ : ℂ | ‖ξ‖ < 1} hBopen {0} hS0 hSfin j H
      (PartialWord [j] H) 0 le_rfl (by norm_num) hC1 (fun z _ => rfl) (hHloc 1)
      (hPWloc1 j) ?_
    intro z₀ hz₀
    rw [Set.mem_singleton_iff] at hz₀
    subst hz₀
    refine ⟨MH, 1 / 2, by norm_num, ?_⟩
    intro z hz1 hz2
    rw [sub_zero] at hz1 hz2 ⊢
    rw [neg_zero, Real.rpow_zero, mul_one]
    refine hMH z ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  -- ## Step 10 preparation: the circlewise Fourier coefficient of the series,
  -- computed by term-by-term integration, is `Thm2SeriesCircleFourierCoef`;
  -- `hHdef` turns the explicit `if`-expression of its statement back into `H`
  obtain ⟨hpolar, hFour⟩ := Thm2SeriesCircleFourierCoef n p hn hp A hsum
  rw [← hHdef] at hFour
  -- ## Step 6: measurability of the disc, used by the Fatou argument below
  have hBdmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} := hBopen.measurableSet
  -- ## Step 5 (continued): the polar form of the two Wirtinger derivatives of
  -- each summand is `Thm2TermPolarWirtingerDerivs`
  have hpolDZ := fun (k : ℕ) (r : ℝ) (hr : 0 < r) (θ : ℝ) =>
    Thm2TermPolarWirtingerDerivs n p A k r hr θ
  -- ## Step 7: the energy over the disc of a finite sum of polar-separated
  -- summands is `PolarSeparatedSumEnergy`, which composes the polar change of
  -- variables with finite Parseval and the radial integral
  have hQval := fun (fk : ℕ → ℂ → ℂ) (g1 g2 : ℕ → ℤ) (γ δ : ℕ → ℂ)
      (F : Finset ℕ) (e : ℕ → ℝ) => PolarSeparatedSumEnergy fk g1 g2 γ δ F e
  -- ## Step 6/8: the uniform energy bound and Fatou
  obtain ⟨Etot, hEtot0, hEtotbd, hEtend⟩ : ∃ E : ℝ, 0 ≤ E ∧
      (∀ s : Finset ℕ, ∑ m ∈ s, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 ≤ E) ∧
      Filter.Tendsto (fun N : ℕ => E - ∑ m ∈ Finset.range (N + 1),
        ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) Filter.atTop (nhds 0) := by
    refine ⟨∑' m : ℕ, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2,
      tsum_nonneg (fun m => by positivity),
      fun s => hsum.sum_le_tsum s (fun i _ => by positivity), ?_⟩
    have h := hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := ∑' m : ℕ,
      ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) (f := Filter.atTop (α := ℕ))).sub h
    rw [sub_self] at h2
    exact h2
  obtain ⟨CE, hCE0, hCEbd⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (W D : ℝ), n + 1 ≤ k → 0 ≤ W →
      W ≤ (2 + Real.sqrt (p - 1)) ^ 2 * (k : ℝ) ^ 2 * ‖A (k : ℤ)‖ ^ 2 / 2 →
      b * (k : ℝ) / (n : ℝ) ≤ D →
      2 * Real.pi * W / D ≤ C * (k : ℝ) * ‖A (k : ℤ)‖ ^ 2 := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    refine ⟨Real.pi * (2 + Real.sqrt (p - 1)) ^ 2 * (n : ℝ) / b, by positivity, ?_⟩
    intro k W D hk hW0 hWb hD
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    have hbk : (0 : ℝ) < b * (k : ℝ) / (n : ℝ) := by positivity
    have hD0 : (0 : ℝ) < D := lt_of_lt_of_le hbk hD
    have hnum : (0 : ℝ) ≤ 2 * Real.pi
        * ((2 + Real.sqrt (p - 1)) ^ 2 * (k : ℝ) ^ 2 * ‖A (k : ℤ)‖ ^ 2 / 2) := by
      have := Real.pi_pos
      have := Real.sqrt_nonneg (p - 1)
      positivity
    have hstep : 2 * Real.pi * W / D
        ≤ 2 * Real.pi * ((2 + Real.sqrt (p - 1)) ^ 2 * (k : ℝ) ^ 2 * ‖A (k : ℤ)‖ ^ 2 / 2)
            / (b * (k : ℝ) / (n : ℝ)) := by
      refine div_le_div₀ hnum ?_ hbk hD
      have := Real.pi_pos
      nlinarith
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have hlamlow : ∀ k : ℕ, n + 1 ≤ k → b * (k : ℝ) / (n : ℝ) ≤ 2 * LambdaCoef n k p := by
    intro k hk
    have hnk : n ≤ k := by omega
    have h := hbL (k - n)
    have hcast : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := Nat.cast_sub hnk
    rw [hcast, show n + (k - n) = k from by omega] at h
    have hk1 : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hu : (1 : ℝ) ≤ (k : ℝ) - (n : ℝ) := by linarith
    have hkey : (k : ℝ) ≤ 2 * (n : ℝ) * ((k : ℝ) - (n : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hu
        (show (0 : ℝ) ≤ 2 * (n : ℝ) - 1 by linarith)]
    rw [div_le_iff₀ hn0]
    have h1 : b * (k : ℝ) ≤ b * (2 * (n : ℝ) * ((k : ℝ) - (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hkey hb0.le
    have h2 : 2 * (n : ℝ) * (b * ((k : ℝ) - (n : ℝ))) ≤ 2 * (n : ℝ) * (LambdaCoef n k p) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [h1, h2]
  have hcoefbd : ∀ (k : ℕ) (c : ℝ) (x : ℂ), n + 1 ≤ k →
      |c| ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 → ‖x‖ ≤ ‖A (k : ℤ)‖ →
      ‖((c : ℝ) : ℂ) * x‖ ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 * ‖A (k : ℤ)‖ := by
    intro k c x hk hc hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h0 : (0 : ℝ) ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 := by
      have := Real.sqrt_nonneg (p - 1)
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      positivity
    exact mul_le_mul hc hx (norm_nonneg _) h0
  have hWbound : ∀ (k : ℕ) (γ δ : ℂ),
      ‖γ‖ ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 * ‖A (k : ℤ)‖ →
      ‖δ‖ ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 * ‖A (k : ℤ)‖ →
      ‖γ‖ ^ 2 + ‖δ‖ ^ 2
        ≤ (2 + Real.sqrt (p - 1)) ^ 2 * (k : ℝ) ^ 2 * ‖A (k : ℤ)‖ ^ 2 / 2 := by
    intro k γ δ h1 h2
    have h0 : (0 : ℝ) ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 * ‖A (k : ℤ)‖ :=
      le_trans (norm_nonneg γ) h1
    nlinarith [norm_nonneg γ, norm_nonneg δ]
  have habsbd : ∀ k : ℕ, n + 1 ≤ k →
      |(LambdaCoef n k p + (k : ℝ) - (n : ℝ)) / 2| ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2
      ∧ |(LambdaCoef n k p - (k : ℝ) - (n : ℝ)) / 2| ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2
      ∧ |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2| ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2
      ∧ |(LambdaCoef n k p + (n : ℝ) + (k : ℝ)) / 2|
          ≤ (2 + Real.sqrt (p - 1)) * (k : ℝ) / 2 := by
    intro k hk
    have hnk : (n : ℝ) ≤ (k : ℝ) := by
      have : n ≤ k := by omega
      exact_mod_cast this
    have hl0 : 0 ≤ LambdaCoef n k p := by
      have h1 := (hlambd k hk).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
    have hlup := (hlambd k hk).2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith
  have hDZmeasgen : ∀ f : ℂ → ℂ, Measurable (DZ f) ∧ Measurable (DZbar f) := by
    intro f
    have h1 := measurable_fderiv_apply_const ℝ f (1 : ℂ)
    have h2 := measurable_fderiv_apply_const ℝ f Complex.I
    have e1 : DZ f = fun z : ℂ =>
        (1 / 2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) := rfl
    have e2 : DZbar f = fun z : ℂ =>
        (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) := rfl
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact (h1.sub (h2.const_mul _)).const_mul _
    · rw [e2]
      exact (h1.add (h2.const_mul _)).const_mul _
  have hcastk : ∀ m : ℕ, (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := hcast
  have hcastA2 : ∀ m : ℕ, A (((n + m : ℕ)) : ℤ) = A ((n : ℤ) + (m : ℤ)) := by
    intro m
    congr 1
  have hperterm : ∀ (m : ℕ) (γ δ : ℂ) (D : ℝ), 1 ≤ m →
      b * (((n + m : ℕ)) : ℝ) / (n : ℝ) ≤ D →
      ‖γ‖ ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2 * ‖A (((n + m : ℕ)) : ℤ)‖ →
      ‖δ‖ ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2 * ‖A (((n + m : ℕ)) : ℤ)‖ →
      ENNReal.ofReal (2 * Real.pi * (‖γ‖ ^ 2 + ‖δ‖ ^ 2) / D)
        ≤ ENNReal.ofReal (CE * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) := by
    intro m γ δ D hm hD hγ hδ
    refine ENNReal.ofReal_le_ofReal ?_
    have hk : n + 1 ≤ n + m := by omega
    have hW := hWbound (n + m) γ δ hγ hδ
    have h := hCEbd (n + m) (‖γ‖ ^ 2 + ‖δ‖ ^ 2) D hk (by positivity) hW hD
    refine le_trans h (le_of_eq ?_)
    rw [hcastk m, hcastA2 m]
    ring
  have hQbd : ∀ (fk : ℕ → ℂ → ℂ) (g1 g2 : ℕ → ℤ) (γ δ : ℕ → ℂ) (e : ℕ → ℝ)
      (F : Finset ℕ) (S : ℝ),
      (∀ k, Measurable (fk k)) →
      (∀ m ∈ F, 1 ≤ m) →
      (∀ m ∈ F, -1 < e m) →
      (∀ m ∈ F, b * (((n + m : ℕ)) : ℝ) / (n : ℝ) ≤ 2 * e m + 2) →
      (∀ m ∈ F, ∀ m' ∈ F, g1 m = g1 m' → m = m') →
      (∀ m ∈ F, ∀ m' ∈ F, g2 m = g2 m' → m = m') →
      (∀ m ∈ F, ∀ m' ∈ F, g1 m ≠ g2 m') →
      (∀ m ∈ F, ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
        fk m ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          = ((r ^ (e m) : ℝ) : ℂ)
            * (γ m * Complex.exp (((g1 m : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + δ m * Complex.exp (((g2 m : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) →
      (∀ m ∈ F, ‖γ m‖ ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2
          * ‖A (((n + m : ℕ)) : ℤ)‖) →
      (∀ m ∈ F, ‖δ m‖ ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2
          * ‖A (((n + m : ℕ)) : ℤ)‖) →
      0 ≤ S →
      (∑ m ∈ F, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 ≤ S) →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal
          (‖∑ m ∈ F, fk m ξ‖ ^ 2))
        ≤ ENNReal.ofReal (CE * S) := by
    intro fk g1 g2 γ δ e F S hmk hm1 he hD hi1 hi2 hi12 hpp hγ hδ hS0 hSbd
    rw [hQval fk g1 g2 γ δ F e hmk he hi1 hi2 hi12 hpp]
    refine le_trans (Finset.sum_le_sum (g := fun m : ℕ =>
      ENNReal.ofReal (CE * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)))
      (fun m hm => ?_)) ?_
    · exact hperterm m (γ m) (δ m) (2 * e m + 2) (hm1 m hm) (hD m hm) (hγ m hm) (hδ m hm)
    · rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hSbd hCE0
  have hDZT0 : ∀ ξ : ℂ, ξ ≠ 0 →
      DZ (Thm2Term n p A (n + 0)) ξ = 0 ∧ DZbar (Thm2Term n p A (n + 0)) ξ = 0 := by
    intro ξ hξ
    have e1 : DZ (Thm2Term n p A (n + 0)) ξ
        = (1 / 2 : ℂ) * (fderiv ℝ (Thm2Term n p A (n + 0)) ξ 1
          - Complex.I * fderiv ℝ (Thm2Term n p A (n + 0)) ξ Complex.I) := rfl
    have e2 : DZbar (Thm2Term n p A (n + 0)) ξ
        = (1 / 2 : ℂ) * (fderiv ℝ (Thm2Term n p A (n + 0)) ξ 1
          + Complex.I * fderiv ℝ (Thm2Term n p A (n + 0)) ξ Complex.I) := rfl
    rw [e1, e2, hfd0 ξ hξ]
    simp
  have hfdsummable : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      Summable (fun m : ℕ => fderiv ℝ (Thm2Term n p A (n + m)) ξ) := by
    intro ξ hx hx1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hx
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hfdbd m ξ hx) ?_)
    have hid : ∀ m : ℕ, (2 * (4 + Real.sqrt (p - 1)) * ‖ξ‖ ^ (-(1 : ℝ)))
          * (((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p))
        = 2 * ((4 + Real.sqrt (p - 1)) * ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)) := by
      intro m
      have hsp : ‖ξ‖ ^ (LambdaCoef n (n + m) p - 1)
          = ‖ξ‖ ^ (LambdaCoef n (n + m) p) * ‖ξ‖ ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hr]
        congr 1
      rw [hsp]
      ring
    exact Summable.congr ((hgeo1 ‖ξ‖ hr hx1).mul_left _) hid
  have hHS3 : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      HasSum (fun m : ℕ => Thm2Term n p A (n + m) ξ) (H ξ)
      ∧ HasSum (fun m : ℕ => DZ (Thm2Term n p A (n + m)) ξ) (DZ H ξ)
      ∧ HasSum (fun m : ℕ => DZbar (Thm2Term n p A (n + m)) ξ) (DZbar H ξ) := by
    intro ξ hx hx1
    have hHS : HasSum (fun m : ℕ => fderiv ℝ (Thm2Term n p A (n + m)) ξ)
        (fderiv ℝ H ξ) := by
      rw [(hHfd ξ hx hx1).fderiv]
      exact (hfdsummable ξ hx hx1).hasSum
    have h1 := (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).hasSum hHS
    have h2 := (ContinuousLinearMap.apply ℝ ℂ Complex.I).hasSum hHS
    simp only [ContinuousLinearMap.apply_apply] at h1 h2
    refine ⟨?_, ?_, ?_⟩
    · rw [hHval ξ hx]
      exact (Summable.of_norm (hnormsum ξ hx hx1)).hasSum
    · have h3 := (h1.mul_left ((1 : ℂ) / 2)).sub (h2.mul_left ((1 : ℂ) / 2 * Complex.I))
      have heq : (fun m : ℕ => (1 : ℂ) / 2 * fderiv ℝ (Thm2Term n p A (n + m)) ξ 1
            - (1 : ℂ) / 2 * Complex.I * fderiv ℝ (Thm2Term n p A (n + m)) ξ Complex.I)
          = (fun m : ℕ => DZ (Thm2Term n p A (n + m)) ξ) := by
        funext m
        have e1 : DZ (Thm2Term n p A (n + m)) ξ
            = (1 / 2 : ℂ) * (fderiv ℝ (Thm2Term n p A (n + m)) ξ 1
              - Complex.I * fderiv ℝ (Thm2Term n p A (n + m)) ξ Complex.I) := rfl
        rw [e1]
        ring
      have hval : (1 : ℂ) / 2 * fderiv ℝ H ξ 1
          - (1 : ℂ) / 2 * Complex.I * fderiv ℝ H ξ Complex.I = DZ H ξ := by
        have e1 : DZ H ξ = (1 / 2 : ℂ) * (fderiv ℝ H ξ 1
            - Complex.I * fderiv ℝ H ξ Complex.I) := rfl
        rw [e1]
        ring
      rw [← heq, ← hval]
      exact h3
    · have h3 := (h1.mul_left ((1 : ℂ) / 2)).add (h2.mul_left ((1 : ℂ) / 2 * Complex.I))
      have heq : (fun m : ℕ => (1 : ℂ) / 2 * fderiv ℝ (Thm2Term n p A (n + m)) ξ 1
            + (1 : ℂ) / 2 * Complex.I * fderiv ℝ (Thm2Term n p A (n + m)) ξ Complex.I)
          = (fun m : ℕ => DZbar (Thm2Term n p A (n + m)) ξ) := by
        funext m
        have e2 : DZbar (Thm2Term n p A (n + m)) ξ
            = (1 / 2 : ℂ) * (fderiv ℝ (Thm2Term n p A (n + m)) ξ 1
              + Complex.I * fderiv ℝ (Thm2Term n p A (n + m)) ξ Complex.I) := rfl
        rw [e2]
        ring
      have hval : (1 : ℂ) / 2 * fderiv ℝ H ξ 1
          + (1 : ℂ) / 2 * Complex.I * fderiv ℝ H ξ Complex.I = DZbar H ξ := by
        have e2 : DZbar H ξ = (1 / 2 : ℂ) * (fderiv ℝ H ξ 1
            + Complex.I * fderiv ℝ H ξ Complex.I) := rfl
        rw [e2]
        ring
      rw [← heq, ← hval]
      exact h3
  have hshift : ∀ (f : ℕ → ℂ), f 0 = 0 → ∀ M : ℕ,
      (∑ m ∈ Finset.range (M + 1), f m) = ∑ m ∈ Finset.Ico 1 (M + 1), f m := by
    intro f hf0 M
    rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < M + 1), hf0, zero_add]
  have hDZtend : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      Filter.Tendsto (fun M : ℕ => ∑ m ∈ Finset.Ico 1 (M + 1),
          DZ (Thm2Term n p A (n + m)) ξ) Filter.atTop (nhds (DZ H ξ))
      ∧ Filter.Tendsto (fun M : ℕ => ∑ m ∈ Finset.Ico 1 (M + 1),
          DZbar (Thm2Term n p A (n + m)) ξ) Filter.atTop (nhds (DZbar H ξ)) := by
    intro ξ hx hx1
    obtain ⟨_, h2, h3⟩ := hHS3 ξ hx hx1
    exact ⟨(h2.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr
        (fun M => hshift _ (hDZT0 ξ hx).1 M),
      (h3.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr
        (fun M => hshift _ (hDZT0 ξ hx).2 M)⟩
  have hQDZ1 : ∀ (F : Finset ℕ) (S : ℝ), (∀ m ∈ F, 1 ≤ m) → 0 ≤ S →
      (∑ m ∈ F, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 ≤ S) →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal
      (‖∑ m ∈ F, DZ (Thm2Term n p A (n + m)) ξ‖ ^ 2))
      ≤ ENNReal.ofReal (CE * S) := by
    intro F S hF1 hS0 hSbd
    refine hQbd (fun m => DZ (Thm2Term n p A (n + m)))
      (fun m => (((n + m : ℕ)) : ℤ) - (n : ℤ) - 1)
      (fun m => -(((n + m : ℕ)) : ℤ) - (n : ℤ) - 1)
      (fun m => (((LambdaCoef n (n + m) p + (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2 : ℝ) : ℂ)
        * A (((n + m : ℕ)) : ℤ))
      (fun m => (((LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2 : ℝ) : ℂ)
        * ((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A (((n + m : ℕ)) : ℤ)))
      (fun m => LambdaCoef n (n + m) p - 1) F S
      (fun k => (hDZmeasgen _).1) hF1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS0 hSbd
    · intro m hm
      have hm1 := hF1 m hm
      have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
    · intro m hm
      have hm1 := hF1 m hm
      have := hlamlow (n + m) (by omega)
      linarith
    · intro m _ m' _ h
      omega
    · intro m _ m' _ h
      omega
    · intro m hm m' hm'
      have hm1 := hF1 m hm
      have hm1' := hF1 m' hm'
      omega
    · intro m _ r hr θ
      exact (hpolDZ (n + m) r hr θ).1
    · intro m hm
      have hm1 := hF1 m hm
      exact hcoefbd (n + m) _ _ (by omega) (habsbd (n + m) (by omega)).1 (le_refl _)
    · intro m hm
      have hm1 := hF1 m hm
      have hk : n + 1 ≤ n + m := by omega
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_conj]
      have h1 := (habsbd (n + m) hk).2.1
      have h2 := hepsle m
      have h3 : (0 : ℝ) ≤ ‖A (((n + m : ℕ)) : ℤ)‖ := norm_nonneg _
      have h5 : (0 : ℝ) ≤ |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2| :=
        abs_nonneg _
      have h6 : |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2|
            * |EpsCoef n (n + m) p|
          ≤ |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2| := by
        calc |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2|
              * |EpsCoef n (n + m) p|
            ≤ |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2| * 1 :=
              mul_le_mul_of_nonneg_left h2 h5
          _ = |(LambdaCoef n (n + m) p - (((n + m : ℕ)) : ℝ) - (n : ℝ)) / 2| := mul_one _
      exact mul_le_mul_of_nonneg_right (le_trans h6 h1) h3
  have hQDZ2 : ∀ (F : Finset ℕ) (S : ℝ), (∀ m ∈ F, 1 ≤ m) → 0 ≤ S →
      (∑ m ∈ F, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 ≤ S) →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal
      (‖∑ m ∈ F, DZbar (Thm2Term n p A (n + m)) ξ‖ ^ 2))
      ≤ ENNReal.ofReal (CE * S) := by
    intro F S hF1 hS0 hSbd
    refine hQbd (fun m => DZbar (Thm2Term n p A (n + m)))
      (fun m => (((n + m : ℕ)) : ℤ) - (n : ℤ) + 1)
      (fun m => -(((n + m : ℕ)) : ℤ) - (n : ℤ) + 1)
      (fun m => (((LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) / 2 : ℝ) : ℂ)
        * A (((n + m : ℕ)) : ℤ))
      (fun m => (((LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2 : ℝ) : ℂ)
        * ((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A (((n + m : ℕ)) : ℤ)))
      (fun m => LambdaCoef n (n + m) p - 1) F S
      (fun k => (hDZmeasgen _).2) hF1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS0 hSbd
    · intro m hm
      have hm1 := hF1 m hm
      have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
    · intro m hm
      have hm1 := hF1 m hm
      have := hlamlow (n + m) (by omega)
      linarith
    · intro m _ m' _ h
      omega
    · intro m _ m' _ h
      omega
    · intro m hm m' hm'
      have hm1 := hF1 m hm
      have hm1' := hF1 m' hm'
      omega
    · intro m _ r hr θ
      exact (hpolDZ (n + m) r hr θ).2
    · intro m hm
      have hm1 := hF1 m hm
      exact hcoefbd (n + m) _ _ (by omega) (habsbd (n + m) (by omega)).2.2.1 (le_refl _)
    · intro m hm
      have hm1 := hF1 m hm
      have hk : n + 1 ≤ n + m := by omega
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Complex.norm_conj]
      have h1 := (habsbd (n + m) hk).2.2.2
      have h2 := hepsle m
      have h3 : (0 : ℝ) ≤ ‖A (((n + m : ℕ)) : ℤ)‖ := norm_nonneg _
      have h5 : (0 : ℝ) ≤ |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2| :=
        abs_nonneg _
      have h6 : |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2|
            * |EpsCoef n (n + m) p|
          ≤ |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2| := by
        calc |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2|
              * |EpsCoef n (n + m) p|
            ≤ |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2| * 1 :=
              mul_le_mul_of_nonneg_left h2 h5
          _ = |(LambdaCoef n (n + m) p + (n : ℝ) + (((n + m : ℕ)) : ℝ)) / 2| := mul_one _
      exact mul_le_mul_of_nonneg_right (le_trans h6 h1) h3
  have hTkmeas : ∀ k : ℕ, Measurable (Thm2Term n p A k) := by
    intro k
    have h1 : Continuous (fun z : ℂ => A (k : ℤ) * z ^ k
        + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ z) ^ k) := by
      exact (continuous_const.mul (continuous_id.pow k)).add
        (continuous_const.mul ((Complex.continuous_conj).pow k))
    have h2 : Measurable
        (fun z : ℂ => ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) := by
      refine Complex.measurable_ofReal.comp ?_
      exact (continuous_norm.measurable).pow measurable_const
    have h3 : Measurable (fun z : ℂ => z ^ (-(n : ℤ))) := by
      have hz : (fun z : ℂ => z ^ (-(n : ℤ))) = fun z : ℂ => (z ^ n)⁻¹ := by
        funext z
        rw [zpow_neg, zpow_natCast]
      rw [hz]
      exact (measurable_id.pow_const n).inv
    exact (h1.measurable.mul h2).mul h3
  have hpolT : ∀ (m : ℕ) (r : ℝ), 0 < r → ∀ θ : ℝ,
      Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ((r ^ (LambdaCoef n (n + m) p) : ℝ) : ℂ)
          * (A ((n : ℤ) + (m : ℤ))
                * Complex.exp (((((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ)
                    * (θ : ℂ) * Complex.I)
            + (((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
                * Complex.exp (((-((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ)
                    * (θ : ℂ) * Complex.I)) := by
    intro m r hr θ
    have h := hpolar m (n : ℤ) r hr θ
    rw [show ((n : ℤ) - (n : ℤ)) = 0 from sub_self _, Int.cast_zero, zero_mul, zero_mul,
      Complex.exp_zero, mul_one] at h
    rw [h]
    ring
  have hQT : ∀ (F : Finset ℕ) (S : ℝ), (∀ m ∈ F, 1 ≤ m) → 0 ≤ S →
      (∑ m ∈ F, ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 ≤ S) →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal
      (‖∑ m ∈ F, Thm2Term n p A (n + m) ξ‖ ^ 2))
      ≤ ENNReal.ofReal (CE * S) := by
    intro F S hF1 hS0 hSbd
    refine hQbd (fun m => Thm2Term n p A (n + m))
      (fun m => ((n : ℤ) + (m : ℤ)) - (n : ℤ))
      (fun m => -((n : ℤ) + (m : ℤ)) - (n : ℤ))
      (fun m => A ((n : ℤ) + (m : ℤ)))
      (fun m => ((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
      (fun m => LambdaCoef n (n + m) p) F S
      (fun k => hTkmeas (n + k)) hF1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS0 hSbd
    · intro m _
      have := hL0 m
      linarith
    · intro m hm
      have hm1 := hF1 m hm
      have := hlamlow (n + m) (by omega)
      linarith
    · intro m _ m' _ h
      omega
    · intro m _ m' _ h
      omega
    · intro m hm m' hm'
      have hm1 := hF1 m hm
      have hm1' := hF1 m' hm'
      omega
    · intro m _ r hr θ
      exact hpolT m r hr θ
    · intro m hm
      have hm1 := hF1 m hm
      rw [← hcastA2 m]
      have h0 : (0 : ℝ) ≤ ‖A (((n + m : ℕ)) : ℤ)‖ := norm_nonneg _
      have hkk : (2 : ℝ) ≤ (((n + m : ℕ)) : ℝ) := by
        have h2 : 2 ≤ n + m := by omega
        exact_mod_cast h2
      have hsq : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
      have hc1 : (1 : ℝ) ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2 := by
        have h1 : (2 : ℝ) * 2 ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) :=
          mul_le_mul (by linarith) hkk (by norm_num) (by linarith)
        linarith
      calc ‖A (((n + m : ℕ)) : ℤ)‖ = 1 * ‖A (((n + m : ℕ)) : ℤ)‖ := (one_mul _).symm
        _ ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2
              * ‖A (((n + m : ℕ)) : ℤ)‖ := mul_le_mul_of_nonneg_right hc1 h0
    · intro m hm
      have hm1 := hF1 m hm
      rw [← hcastA2 m, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
      have h0 : (0 : ℝ) ≤ ‖A (((n + m : ℕ)) : ℤ)‖ := norm_nonneg _
      have hkk : (2 : ℝ) ≤ (((n + m : ℕ)) : ℝ) := by
        have h2 : 2 ≤ n + m := by omega
        exact_mod_cast h2
      have hsq : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
      have hc1 : (1 : ℝ) ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) / 2 := by
        have h1 : (2 : ℝ) * 2 ≤ (2 + Real.sqrt (p - 1)) * (((n + m : ℕ)) : ℝ) :=
          mul_le_mul (by linarith) hkk (by norm_num) (by linarith)
        linarith
      exact mul_le_mul_of_nonneg_right (le_trans (hepsle m) hc1) h0
  have hfat : (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖DZ H ξ‖ ^ 2))
        ≤ ENNReal.ofReal (CE * Etot)
      ∧ (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖DZbar H ξ‖ ^ 2))
        ≤ ENNReal.ofReal (CE * Etot) := by
    constructor
    · have hae1 : ∀ᵐ ξ ∂(MeasureTheory.volume.restrict {ξ : ℂ | ‖ξ‖ < 1}),
          ENNReal.ofReal (‖DZ H ξ‖ ^ 2)
            = Filter.liminf (fun M : ℕ => ENNReal.ofReal
                (‖∑ m ∈ Finset.Ico 1 (M + 1), DZ (Thm2Term n p A (n + m)) ξ‖ ^ 2))
                Filter.atTop := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
          MeasureTheory.ae_restrict_mem hBdmeas] with ξ hx hmemB
        have hb : ‖ξ‖ < 1 := hmemB
        refine (Filter.Tendsto.liminf_eq ?_).symm
        exact (ENNReal.continuous_ofReal.tendsto (‖DZ H ξ‖ ^ 2)).comp
          (((hDZtend ξ hx hb).1.norm).pow 2)
      rw [MeasureTheory.lintegral_congr_ae hae1]
      refine le_trans (MeasureTheory.lintegral_liminf_le (fun M => ?_)) ?_
      · exact ENNReal.measurable_ofReal.comp
          (((Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).1)).norm).pow_const 2)
      · exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall
          (fun M => hQDZ1 (Finset.Ico 1 (M + 1)) Etot
            (fun m hm => (Finset.mem_Ico.mp hm).1) hEtot0 (hEtotbd _)))
    · have hae2 : ∀ᵐ ξ ∂(MeasureTheory.volume.restrict {ξ : ℂ | ‖ξ‖ < 1}),
          ENNReal.ofReal (‖DZbar H ξ‖ ^ 2)
            = Filter.liminf (fun M : ℕ => ENNReal.ofReal
                (‖∑ m ∈ Finset.Ico 1 (M + 1), DZbar (Thm2Term n p A (n + m)) ξ‖ ^ 2))
                Filter.atTop := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
          MeasureTheory.ae_restrict_mem hBdmeas] with ξ hx hmemB
        have hb : ‖ξ‖ < 1 := hmemB
        refine (Filter.Tendsto.liminf_eq ?_).symm
        exact (ENNReal.continuous_ofReal.tendsto (‖DZbar H ξ‖ ^ 2)).comp
          (((hDZtend ξ hx hb).2.norm).pow 2)
      rw [MeasureTheory.lintegral_congr_ae hae2]
      refine le_trans (MeasureTheory.lintegral_liminf_le (fun M => ?_)) ?_
      · exact ENNReal.measurable_ofReal.comp
          (((Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).2)).norm).pow_const 2)
      · exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall
          (fun M => hQDZ2 (Finset.Ico 1 (M + 1)) Etot
            (fun m hm => (Finset.mem_Ico.mp hm).1) hEtot0 (hEtotbd _)))
  -- ## Step 11: the `W^{1,2}` convergence of the series
  obtain ⟨Phi, Psi, hPhi, hPsi⟩ : ∃ Phi Psi : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ,
      (∀ L : ℂ →L[ℝ] ℂ, Phi L = (1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I))
      ∧ (∀ L : ℂ →L[ℝ] ℂ, Psi L = (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) := by
    refine ⟨(1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ))
        - ((1 / 2 : ℂ) * Complex.I) • (ContinuousLinearMap.apply ℝ ℂ Complex.I),
      (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ))
        + ((1 / 2 : ℂ) * Complex.I) • (ContinuousLinearMap.apply ℝ ℂ Complex.I),
      fun L => ?_, fun L => ?_⟩ <;>
      simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.apply_apply,
        smul_eq_mul] <;>
      ring
  have hDZPhi : ∀ (f : ℂ → ℂ) (z : ℂ),
      DZ f z = Phi (fderiv ℝ f z) ∧ DZbar f z = Psi (fderiv ℝ f z) := by
    intro f z
    exact ⟨(hPhi (fderiv ℝ f z)).symm, (hPsi (fderiv ℝ f z)).symm⟩
  have hDZfin : ∀ (s : Finset ℕ) (ξ : ℂ), ξ ≠ 0 →
      DZ (fun z : ℂ => ∑ m ∈ s, Thm2Term n p A (n + m) z) ξ
          = ∑ m ∈ s, DZ (Thm2Term n p A (n + m)) ξ
      ∧ DZbar (fun z : ℂ => ∑ m ∈ s, Thm2Term n p A (n + m) z) ξ
          = ∑ m ∈ s, DZbar (Thm2Term n p A (n + m)) ξ := by
    intro s ξ hξ
    have he : fderiv ℝ (fun z : ℂ => ∑ m ∈ s, Thm2Term n p A (n + m) z) ξ
        = ∑ m ∈ s, fderiv ℝ (Thm2Term n p A (n + m)) ξ :=
      (HasFDerivAt.fun_sum (fun m _ => hTfderiv m ξ hξ)).fderiv
    constructor
    · rw [(hDZPhi _ ξ).1, he, map_sum]
      exact Finset.sum_congr rfl (fun m _ => ((hDZPhi _ ξ).1).symm)
    · rw [(hDZPhi _ ξ).2, he, map_sum]
      exact Finset.sum_congr rfl (fun m _ => ((hDZPhi _ ξ).2).symm)
  have hreindex : ∀ (F : ℕ → ℂ) (N : ℕ),
      (∑ k ∈ Finset.Icc n (n + N), F k) = ∑ m ∈ Finset.range (N + 1), F (n + m) := by
    intro F N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [show n + (N + 1) = (n + N) + 1 from by omega,
          Finset.sum_Icc_succ_top (by omega : n ≤ (n + N) + 1), ih,
          Finset.sum_range_succ (f := fun m => F (n + m)) (n := N + 1),
          show (n + N) + 1 = n + (N + 1) from by omega]
  have hfatbound : ∀ (u : ℕ → ℂ → ℂ) (G : ℂ → ℂ) (c : ℝ),
      (∀ M, Measurable (u M)) →
      (∀ M, (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖u M ξ‖ ^ 2))
        ≤ ENNReal.ofReal c) →
      (∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
        Filter.Tendsto (fun M : ℕ => u M ξ) Filter.atTop (nhds (G ξ))) →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖G ξ‖ ^ 2)) ≤ ENNReal.ofReal c := by
    intro u G c hum hub hconv
    have hae : ∀ᵐ ξ ∂(MeasureTheory.volume.restrict {ξ : ℂ | ‖ξ‖ < 1}),
        ENNReal.ofReal (‖G ξ‖ ^ 2)
          = Filter.liminf (fun M : ℕ => ENNReal.ofReal (‖u M ξ‖ ^ 2)) Filter.atTop := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
        MeasureTheory.ae_restrict_mem hBdmeas] with ξ hx hmemB
      have hb : ‖ξ‖ < 1 := hmemB
      refine (Filter.Tendsto.liminf_eq ?_).symm
      exact (ENNReal.continuous_ofReal.tendsto (‖G ξ‖ ^ 2)).comp
        (((hconv ξ hx hb).norm).pow 2)
    rw [MeasureTheory.lintegral_congr_ae hae]
    refine le_trans (MeasureTheory.lintegral_liminf_le (fun M =>
      ENNReal.measurable_ofReal.comp (((hum M).norm).pow_const 2))) ?_
    exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hub)
  have hbochner : ∀ (G : ℂ → ℂ) (c : ℝ),
      MeasureTheory.AEStronglyMeasurable (fun ξ : ℂ => ‖G ξ‖ ^ 2)
        (MeasureTheory.volume.restrict {ξ : ℂ | ‖ξ‖ < 1}) → 0 ≤ c →
      (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖G ξ‖ ^ 2)) ≤ ENNReal.ofReal c →
      (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖G ξ‖ ^ 2) ≤ c := by
    intro G c hGm hc0 hb
    have hint : MeasureTheory.IntegrableOn (fun ξ : ℂ => ‖G ξ‖ ^ 2)
        {ξ : ℂ | ‖ξ‖ < 1} MeasureTheory.volume := by
      refine ⟨hGm, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have hs : ∀ ξ : ℂ, ‖‖G ξ‖ ^ 2‖ₑ = ENNReal.ofReal (‖G ξ‖ ^ 2) :=
        fun ξ => Real.enorm_eq_ofReal (by positivity)
      rw [MeasureTheory.lintegral_congr (fun ξ => hs ξ)]
      exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
    refine (ENNReal.ofReal_le_ofReal_iff hc0).mp ?_
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ξ => by positivity))]
    exact hb
  have hint0 : ∀ G : ℂ → ℂ, 0 ≤ ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖G ξ‖ ^ 2 := fun G =>
    MeasureTheory.setIntegral_nonneg hBdmeas (fun x _ => by positivity)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## (a): `H` is continuous on `𝔹`
    exact hHcontOn
  · exact hContB
  · -- ## (c): `H ∈ W^{1,2}_loc(𝔹)`
    refine ⟨fun w => PartialWord w H, rfl, ?_, ?_⟩
    · intro w hw
      match w with
      | [] => exact hHloc 2
      | [j] => exact hPWloc2 j
      | (a :: c :: tl) =>
          simp only [List.length_cons] at hw
          omega
    · intro w j hw
      match w with
      | [] => exact hweak j
      | (a :: tl) =>
          simp only [List.length_cons] at hw
          omega
  · -- ## (d): the Dirichlet energy of `H` is finite
    refine ⟨?_, ?_⟩
    · exact ((((hDZmeasgen H).1.norm).pow_const 2).add
        (((hDZmeasgen H).2.norm).pow_const 2)).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have hsplit : ∀ ξ : ℂ, ‖‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2‖ₑ
          = ENNReal.ofReal (‖DZ H ξ‖ ^ 2) + ENNReal.ofReal (‖DZbar H ξ‖ ^ 2) := by
        intro ξ
        rw [Real.enorm_eq_ofReal (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [MeasureTheory.lintegral_congr (fun ξ => hsplit ξ),
        MeasureTheory.lintegral_add_left
          (f := fun ξ : ℂ => ENNReal.ofReal (‖DZ H ξ‖ ^ 2))
          (ENNReal.measurable_ofReal.comp (((hDZmeasgen H).1.norm).pow_const 2))]
      exact ENNReal.add_lt_top.mpr
        ⟨lt_of_le_of_lt hfat.1 ENNReal.ofReal_lt_top,
          lt_of_le_of_lt hfat.2 ENNReal.ofReal_lt_top⟩
  · -- ## (e): the Fourier coefficients of index `|k| ≥ n`
    intro j hj r hr
    rw [Int.abs_eq_natAbs] at hj
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      positivity
    rw [hFour j r hr.1 hr.2]
    rcases le_or_gt 0 j with hj0 | hj0
    · obtain ⟨m₀, hm0eq⟩ : ∃ m : ℕ, (n : ℤ) + (m : ℤ) = j := ⟨(j - (n : ℤ)).toNat, by omega⟩
      have hsingle : ∀ m : ℕ, m ≠ m₀ →
          (((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
            * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
              + (if ((n : ℤ) + (m : ℤ)) = -j then
                  ((EpsCoef n (n + m) p : ℝ) : ℂ)
                    * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0))) = 0 := by
        intro m hm
        rw [if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = j)),
          if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = -j))]
        ring
      rw [tsum_eq_single m₀ hsingle, if_pos hm0eq,
        if_neg (by omega : ¬ ((n : ℤ) + (m₀ : ℤ) = -j)),
        show LambdaCoef n (n + m₀) p = LambdaCoef n j.natAbs p from by
          congr 1
          omega,
        hm0eq]
      field_simp
      push_cast
      ring
    · obtain ⟨m₀, hm0eq⟩ : ∃ m : ℕ, (n : ℤ) + (m : ℤ) = -j :=
        ⟨(-j - (n : ℤ)).toNat, by omega⟩
      have hsingle : ∀ m : ℕ, m ≠ m₀ →
          (((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
            * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
              + (if ((n : ℤ) + (m : ℤ)) = -j then
                  ((EpsCoef n (n + m) p : ℝ) : ℂ)
                    * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0))) = 0 := by
        intro m hm
        rw [if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = j)),
          if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = -j))]
        ring
      have hcc : A j = ((EpsCoef n (-j).natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A (-j)) := by
        have h := hcomp (-j) (by omega)
        rwa [neg_neg] at h
      rw [tsum_eq_single m₀ hsingle,
        if_neg (by omega : ¬ ((n : ℤ) + (m₀ : ℤ) = j)), if_pos hm0eq,
        show LambdaCoef n (n + m₀) p = LambdaCoef n j.natAbs p from by
          congr 1
          omega,
        show EpsCoef n (n + m₀) p = EpsCoef n (-j).natAbs p from by
          congr 1
          omega,
        hm0eq, ← hcc]
      field_simp
      push_cast
      ring
  · -- ## (f): the Fourier coefficients of index `|k| < n` vanish
    intro j hj r hr
    rw [Int.abs_eq_natAbs] at hj
    rw [hFour j r hr.1 hr.2]
    have hzero : ∀ m : ℕ,
        (((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
          * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
            + (if ((n : ℤ) + (m : ℤ)) = -j then
                ((EpsCoef n (n + m) p : ℝ) : ℂ)
                  * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0))) = 0 := by
      intro m
      rw [if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = j)),
        if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ) = -j))]
      ring
    rw [tsum_congr hzero, tsum_zero, mul_zero]
  · -- ## (g): the series converges to `H` in `W^{1,2}(B)`
    -- the tail `Etot - Σ_{m ≤ N}` of the energy sum: nonnegative, dominates every
    -- further block, and tends to `0`
    have hSnn : ∀ N : ℕ, 0 ≤ Etot - ∑ m ∈ Finset.range (N + 1),
        ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 := by
      intro N
      have h := hEtotbd (Finset.range (N + 1))
      linarith
    have hStail : ∀ N M : ℕ, ∑ m ∈ Finset.Ico (N + 1) (M + 1),
        ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2
          ≤ Etot - ∑ m ∈ Finset.range (N + 1),
            ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 := by
      intro N M
      rcases le_or_gt (N + 1) (M + 1) with hle | hlt
      · have hc := Finset.sum_Ico_consecutive
          (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)
          (Nat.zero_le (N + 1)) hle
        rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hc
        have hb := hEtotbd (Finset.range (M + 1))
        linarith
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
        exact hSnn N
    -- the tail of a convergent series, as a limit of blocks
    have htailtend : ∀ (f : ℕ → ℂ) (L : ℂ), HasSum f L → ∀ N : ℕ,
        Filter.Tendsto (fun M : ℕ => ∑ m ∈ Finset.Ico (N + 1) (M + 1), f m) Filter.atTop
          (nhds (L - ∑ m ∈ Finset.range (N + 1), f m)) := by
      intro f L hf N
      have h1 : Filter.Tendsto (fun M : ℕ => ∑ m ∈ Finset.range (M + 1), f m)
          Filter.atTop (nhds L) :=
        hf.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
      have h2 := h1.sub (tendsto_const_nhds
        (x := ∑ m ∈ Finset.range (N + 1), f m) (f := Filter.atTop (α := ℕ)))
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      have hc := Finset.sum_Ico_consecutive f (Nat.zero_le (N + 1))
        (by omega : N + 1 ≤ M + 1)
      rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hc
      rw [← hc]
      ring
    have hHam : MeasureTheory.AEStronglyMeasurable H
        (MeasureTheory.volume.restrict {ξ : ℂ | ‖ξ‖ < 1}) :=
      hHcontOn.aestronglyMeasurable hBdmeas
    -- the three tail bounds, each by finite-sum orthogonality plus Fatou
    have hbd1 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖H ξ - ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) ξ‖ ^ 2)
          ≤ CE * (Etot - ∑ m ∈ Finset.range (N + 1),
            ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) := by
      intro N
      refine hbochner
        (fun ξ : ℂ => H ξ - ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) ξ) _ ?_
        (mul_nonneg hCE0 (hSnn N)) ?_
      · have h2 : Measurable (fun ξ : ℂ => ∑ m ∈ Finset.range (N + 1),
            Thm2Term n p A (n + m) ξ) :=
          Finset.measurable_sum _ (fun m _ => hTkmeas (n + m))
        exact ((hHam.sub h2.aestronglyMeasurable).norm).pow 2
      · refine hfatbound
          (fun M ξ => ∑ m ∈ Finset.Ico (N + 1) (M + 1), Thm2Term n p A (n + m) ξ)
          (fun ξ : ℂ => H ξ - ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) ξ) _
          (fun M => Finset.measurable_sum _ (fun m _ => hTkmeas (n + m))) ?_ ?_
        · intro M
          exact hQT (Finset.Ico (N + 1) (M + 1)) _
            (fun m hm => by
              have h := (Finset.mem_Ico.mp hm).1
              omega) (hSnn N) (hStail N M)
        · intro ξ hx hx1
          exact htailtend _ _ (hHS3 ξ hx hx1).1 N
    have hbd2 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖DZ H ξ - ∑ m ∈ Finset.range (N + 1), DZ (Thm2Term n p A (n + m)) ξ‖ ^ 2)
          ≤ CE * (Etot - ∑ m ∈ Finset.range (N + 1),
            ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) := by
      intro N
      refine hbochner
        (fun ξ : ℂ => DZ H ξ - ∑ m ∈ Finset.range (N + 1),
          DZ (Thm2Term n p A (n + m)) ξ) _ ?_ (mul_nonneg hCE0 (hSnn N)) ?_
      · exact ((((hDZmeasgen H).1.sub
          (Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).1))).norm).pow_const
            2).aestronglyMeasurable
      · refine hfatbound
          (fun M ξ => ∑ m ∈ Finset.Ico (N + 1) (M + 1), DZ (Thm2Term n p A (n + m)) ξ)
          (fun ξ : ℂ => DZ H ξ - ∑ m ∈ Finset.range (N + 1),
            DZ (Thm2Term n p A (n + m)) ξ) _
          (fun M => Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).1)) ?_ ?_
        · intro M
          exact hQDZ1 (Finset.Ico (N + 1) (M + 1)) _
            (fun m hm => by
              have h := (Finset.mem_Ico.mp hm).1
              omega) (hSnn N) (hStail N M)
        · intro ξ hx hx1
          exact htailtend _ _ (hHS3 ξ hx hx1).2.1 N
    have hbd3 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖DZbar H ξ - ∑ m ∈ Finset.range (N + 1), DZbar (Thm2Term n p A (n + m)) ξ‖ ^ 2)
          ≤ CE * (Etot - ∑ m ∈ Finset.range (N + 1),
            ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) := by
      intro N
      refine hbochner
        (fun ξ : ℂ => DZbar H ξ - ∑ m ∈ Finset.range (N + 1),
          DZbar (Thm2Term n p A (n + m)) ξ) _ ?_ (mul_nonneg hCE0 (hSnn N)) ?_
      · exact ((((hDZmeasgen H).2.sub
          (Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).2))).norm).pow_const
            2).aestronglyMeasurable
      · refine hfatbound
          (fun M ξ => ∑ m ∈ Finset.Ico (N + 1) (M + 1), DZbar (Thm2Term n p A (n + m)) ξ)
          (fun ξ : ℂ => DZbar H ξ - ∑ m ∈ Finset.range (N + 1),
            DZbar (Thm2Term n p A (n + m)) ξ) _
          (fun M => Finset.measurable_sum _ (fun m _ => (hDZmeasgen _).2)) ?_ ?_
        · intro M
          exact hQDZ2 (Finset.Ico (N + 1) (M + 1)) _
            (fun m hm => by
              have h := (Finset.mem_Ico.mp hm).1
              omega) (hSnn N) (hStail N M)
        · intro ξ hx hx1
          exact htailtend _ _ (hHS3 ξ hx hx1).2.2 N
    -- rewriting the partial sums of the statement, indexed by `Finset.Icc n (n+N)`,
    -- as the blocks `Finset.range (N+1)` used above
    have hrw1 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k ξ‖ ^ 2)
          = (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖H ξ - ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) ξ‖ ^ 2) := by
      intro N
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ξ
      simp only [hreindex (fun k => Thm2Term n p A k ξ) N]
    have hrw2 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZ H ξ
            - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2)
          = (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            ‖DZ H ξ - ∑ m ∈ Finset.range (N + 1), DZ (Thm2Term n p A (n + m)) ξ‖ ^ 2) := by
      intro N
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with ξ hx
      have hfe : (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z)
          = fun z : ℂ => ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) z :=
        funext (fun z => hreindex (fun k => Thm2Term n p A k z) N)
      rw [hfe, (hDZfin (Finset.range (N + 1)) ξ hx).1]
    have hrw3 : ∀ N : ℕ,
        (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
            - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2)
          = (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
            - ∑ m ∈ Finset.range (N + 1), DZbar (Thm2Term n p A (n + m)) ξ‖ ^ 2) := by
      intro N
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with ξ hx
      have hfe : (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z)
          = fun z : ℂ => ∑ m ∈ Finset.range (N + 1), Thm2Term n p A (n + m) z :=
        funext (fun z => hreindex (fun k => Thm2Term n p A k z) N)
      rw [hfe, (hDZfin (Finset.range (N + 1)) ξ hx).2]
    -- the squeeze
    have hc : Filter.Tendsto (fun N : ℕ => CE * (Etot - ∑ m ∈ Finset.range (N + 1),
        ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) Filter.atTop (nhds 0) := by
      have h := hEtend.const_mul CE
      rwa [mul_zero] at h
    have hg := (hc.add hc).add hc
    rw [add_zero, add_zero] at hg
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hg
    · exact add_nonneg (add_nonneg
        (hint0 (fun ξ : ℂ => H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k ξ))
        (hint0 (fun ξ : ℂ => DZ H ξ
          - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ)))
        (hint0 (fun ξ : ℂ => DZbar H ξ
          - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ))
    · rw [hrw1 N, hrw2 N, hrw3 N]
      linarith [hbd1 N, hbd2 N, hbd3 N]
