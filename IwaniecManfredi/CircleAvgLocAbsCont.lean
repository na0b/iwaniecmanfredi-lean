import IwaniecManfredi.WeakPartialEqFDerivAE
import IwaniecManfredi.FourierCoefOfH
import IwaniecManfredi.HRad
import IwaniecManfredi.HAng
import IwaniecManfredi.MollificationL1Convergence
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import IwaniecManfredi.FourierCoefAnnulusRegularity
set_option maxHeartbeats 1600000

open MeasureTheory

/-- Circle averages of a `W^{1,1}_loc` function on an annulus are locally
absolutely continuous in the radius, with the expected radial derivative, and
satisfy the angular integration-by-parts identity.  This is the one-variable
content of the paper's (31) and of the two identities that term-by-term
differentiation (32) amounts to, and it is what replaces Section 3's
`H ∈ C^∞(𝔹 - {0})`: the paper reads that hypothesis at exactly one place,
`paper.tex:265-266`, to get `a_k ∈ C[0,1) ∩ C^∞(0,1)`, and the `C[0,1)` half
comes from continuity alone.

The conclusion is stated as the integral identity rather than as "locally
absolutely continuous" so that it is usable directly: `a_k` is the indefinite
integral of its radial Fourier coefficient, hence differentiable at almost
every radius.  The hypotheses are exactly a `W^{1,1}_loc` witness on the
annulus -- take `D j := D [j]` -- plus continuity and the almost-everywhere
differentiability that item (C2) of the paper's note gives for the inverse of a
quasiconformal homeomorphism. -/
theorem CircleAvgLocAbsCont (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (k : ℤ)
    (H : ℂ → ℂ) (D : Fin 2 → (ℂ → ℂ))
    (hH : MemLpLocOn 1 {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} H)
    (hD : ∀ j : Fin 2, MemLpLocOn 1 {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} (D j))
    (hweak : ∀ j : Fin 2, IsWeakPartialOn {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} j H (D j))
    (hcont : ContinuousOn H {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b})
    (hdiff : ∀ᵐ ξ : ℂ, (a < ‖ξ‖ ∧ ‖ξ‖ < b) → DifferentiableAt ℝ H ξ) :
    (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b,
        IntegrableOn (FourierCoefOfH n (HRad H) k) (Set.uIcc c d) volume) ∧
    (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b,
        FourierCoefOfH n H k d - FourierCoefOfH n H k c
          = ∫ s in c..d, FourierCoefOfH n (HRad H) k s) ∧
    (∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
        HasDerivAt (FourierCoefOfH n H k) (FourierCoefOfH n (HRad H) k r) r) ∧
    (∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
        FourierCoefOfH n (HAng H) k r
          = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r) ∧
    (∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
        IntervalIntegrable
            (fun θ : ℝ => HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            volume 0 (2 * Real.pi) ∧
          IntervalIntegrable
            (fun θ : ℝ => HAng H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            volume 0 (2 * Real.pi)) := by
  set A : Set ℂ := {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} with hAdef
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hAmem : ∀ ζ : ℂ, ζ ∈ A ↔ (a < ‖ζ‖ ∧ ‖ζ‖ < b) := by
    intro ζ
    rw [hAdef]
    exact Iff.rfl
  have hApos : ∀ ζ ∈ A, 0 < ‖ζ‖ := fun ζ hζ => lt_of_le_of_lt ha ((hAmem ζ).mp hζ).1
  -- the circle map and the Fourier weight
  set ci : ℝ → ℝ → ℂ := fun s θ => (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hcidef
  set wt : ℝ → ℂ := fun θ => Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
    with hwtdef
  have hcicont : Continuous (fun p : ℝ × ℝ => ci p.1 p.2) := by
    rw [hcidef]
    fun_prop
  have hwtcont : Continuous wt := by
    rw [hwtdef]
    fun_prop
  have hcinorm : ∀ (s θ : ℝ), ‖ci s θ‖ = |s| := by
    intro s θ
    rw [hcidef]
    simp [Complex.norm_exp_ofReal_mul_I]
  have hwtnorm : ∀ θ : ℝ, ‖wt θ‖ = 1 := by
    intro θ
    rw [hwtdef]
    rw [Complex.norm_exp]
    have : (((((n : ℤ) - k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  -- measurability of the two polar derivatives
  have hdivmeas : Measurable (fun ζ : ℂ => ζ / ((‖ζ‖ : ℝ) : ℂ)) := by
    fun_prop
  have hev : Continuous (fun q : (ℂ →L[ℝ] ℂ) × ℂ => q.1 q.2) :=
    isBoundedBilinearMap_apply.continuous
  have hRadmeas : Measurable (HRad H) := by
    have h1 : Measurable (fun ζ : ℂ => ((fderiv ℝ H ζ), ζ / ((‖ζ‖ : ℝ) : ℂ))) :=
      (measurable_fderiv ℝ H).prodMk hdivmeas
    exact hev.measurable.comp h1
  have hAngmeas : Measurable (HAng H) := by
    have h1 : Measurable (fun ζ : ℂ => ((fderiv ℝ H ζ), Complex.I * ζ)) :=
      (measurable_fderiv ℝ H).prodMk (by fun_prop)
    exact hev.measurable.comp h1
  -- STEP 1: the radial and angular combinations of the weak partials
  have hWP := WeakPartialEqFDerivAE A hAopen H D hH hD hweak hdiff
  have hstep1 : ∀ᵐ ζ : ℂ, ζ ∈ A →
      (HRad H ζ = (ζ.re / ‖ζ‖) • D 0 ζ + (ζ.im / ‖ζ‖) • D 1 ζ ∧
        HAng H ζ = (-ζ.im) • D 0 ζ + ζ.re • D 1 ζ) := by
    filter_upwards [hWP 0, hWP 1, hdiff] with ζ h0 h1 hd hζ
    have hD0 : D 0 ζ = fderiv ℝ H ζ 1 := by
      have h := h0 hζ
      simpa [PartialWord] using h
    have hD1 : D 1 ζ = fderiv ℝ H ζ Complex.I := by
      have h := h1 hζ
      simpa [PartialWord] using h
    have hne : ζ ≠ 0 := by
      intro h
      have := hApos ζ hζ
      rw [h] at this
      simp at this
    have hr : ((‖ζ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne)
    constructor
    · rw [HRad, hD0, hD1]
      have hdec : ζ / ((‖ζ‖ : ℝ) : ℂ)
          = (ζ.re / ‖ζ‖) • (1 : ℂ) + (ζ.im / ‖ζ‖) • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        push_cast
        rw [div_mul_eq_mul_div, ← add_div]
        congr 1
        exact (Complex.re_add_im ζ).symm
      rw [hdec, map_add, map_smul, map_smul]
    · rw [HAng, hD0, hD1]
      have hdec : Complex.I * ζ = (-ζ.im) • (1 : ℂ) + ζ.re • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        simp [Complex.ext_iff]
      rw [hdec, map_add, map_smul, map_smul]
  -- the two polar derivatives are integrable on every compact subset of `A`
  have hintK : ∀ K : Set ℂ, K ⊆ A → IsCompact K →
      IntegrableOn (HRad H) K volume ∧ IntegrableOn (HAng H) K volume := by
    intro K hKA hKc
    have hKm : MeasurableSet K := hKc.measurableSet
    have hK0 : Integrable (K.indicator (D 0)) volume :=
      memLp_one_iff_integrable.mp (hD 0 K hKA hKc)
    have hK1 : Integrable (K.indicator (D 1)) volume :=
      memLp_one_iff_integrable.mp (hD 1 K hKA hKc)
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ K, ‖ζ‖ ≤ M := by
      obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
      refine ⟨max M 0, le_max_right _ _, fun ζ hζ => ?_⟩
      have := hM hζ
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact le_trans this (le_max_left _ _)
    have hbd : Integrable (fun ζ : ℂ =>
        (1 + M) * (‖K.indicator (D 0) ζ‖ + ‖K.indicator (D 1) ζ‖)) volume := by
      have h := (hK0.norm.add hK1.norm)
      exact h.const_mul (1 + M)
    have hle : ∀ (W : ℂ → ℂ), Measurable W →
        (∀ᵐ ζ : ℂ, ζ ∈ K → ‖W ζ‖ ≤ (1 + M) * (‖D 0 ζ‖ + ‖D 1 ζ‖)) →
        IntegrableOn W K volume := by
      intro W hWm hWle
      rw [← integrable_indicator_iff hKm]
      refine Integrable.mono' hbd (hWm.indicator hKm).stronglyMeasurable.aestronglyMeasurable ?_
      filter_upwards [hWle] with ζ hζ
      by_cases hmem : ζ ∈ K
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        exact hζ hmem
      · rw [Set.indicator_of_notMem hmem]
        simp only [norm_zero]
        positivity
    constructor
    · refine hle (HRad H) hRadmeas ?_
      filter_upwards [hstep1] with ζ hζ hmem
      have hA := hKA hmem
      rw [(hζ hA).1]
      have hre : |ζ.re / ‖ζ‖| ≤ 1 := by
        rw [abs_div, abs_norm, div_le_one (hApos ζ hA)]
        exact Complex.abs_re_le_norm ζ
      have him : |ζ.im / ‖ζ‖| ≤ 1 := by
        rw [abs_div, abs_norm, div_le_one (hApos ζ hA)]
        exact Complex.abs_im_le_norm ζ
      calc ‖(ζ.re / ‖ζ‖) • D 0 ζ + (ζ.im / ‖ζ‖) • D 1 ζ‖
          ≤ ‖(ζ.re / ‖ζ‖) • D 0 ζ‖ + ‖(ζ.im / ‖ζ‖) • D 1 ζ‖ := norm_add_le _ _
        _ = |ζ.re / ‖ζ‖| * ‖D 0 ζ‖ + |ζ.im / ‖ζ‖| * ‖D 1 ζ‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖D 0 ζ‖ + 1 * ‖D 1 ζ‖ := by
            have h1 := mul_le_mul_of_nonneg_right hre (norm_nonneg (D 0 ζ))
            have h2 := mul_le_mul_of_nonneg_right him (norm_nonneg (D 1 ζ))
            linarith
        _ ≤ (1 + M) * (‖D 0 ζ‖ + ‖D 1 ζ‖) := by
            nlinarith [hM0, norm_nonneg (D 0 ζ), norm_nonneg (D 1 ζ)]
    · refine hle (HAng H) hAngmeas ?_
      filter_upwards [hstep1] with ζ hζ hmem
      have hA := hKA hmem
      rw [(hζ hA).2]
      have hre : |ζ.re| ≤ M := le_trans (Complex.abs_re_le_norm ζ) (hM ζ hmem)
      have him : |(-ζ.im)| ≤ M := by
        rw [abs_neg]
        exact le_trans (Complex.abs_im_le_norm ζ) (hM ζ hmem)
      calc ‖(-ζ.im) • D 0 ζ + ζ.re • D 1 ζ‖
          ≤ ‖(-ζ.im) • D 0 ζ‖ + ‖ζ.re • D 1 ζ‖ := norm_add_le _ _
        _ = |(-ζ.im)| * ‖D 0 ζ‖ + |ζ.re| * ‖D 1 ζ‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ M * ‖D 0 ζ‖ + M * ‖D 1 ζ‖ := by
            have h1 := mul_le_mul_of_nonneg_right him (norm_nonneg (D 0 ζ))
            have h2 := mul_le_mul_of_nonneg_right hre (norm_nonneg (D 1 ζ))
            linarith
        _ ≤ (1 + M) * (‖D 0 ζ‖ + ‖D 1 ζ‖) := by
            nlinarith [hM0, norm_nonneg (D 0 ζ), norm_nonneg (D 1 ζ)]
  -- periodicity in the angle
  have hperci : ∀ (s θ : ℝ), ci s (θ + 2 * Real.pi) = ci s θ := by
    intro s θ
    rw [hcidef]
    simp only
    congr 1
    rw [show ((↑(θ + 2 * Real.pi) : ℂ)) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_periodic _
  have hperwt : ∀ θ : ℝ, wt (θ + 2 * Real.pi) = wt θ := by
    intro θ
    rw [hwtdef]
    simp only
    have hm := (Complex.exp_periodic.int_mul ((n : ℤ) - k))
      ((((n : ℤ) - k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
    rw [← hm]
    congr 1
    push_cast
    ring
  -- the Fourier coefficient written over a full period
  have hFC : ∀ (F : ℂ → ℂ) (s : ℝ), FourierCoefOfH n F k s
      = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), F (ci s θ) * wt θ := by
    intro F s
    rw [FourierCoefOfH, hcidef, hwtdef]
  -- the compact annulus between two radii
  set Ann : ℝ → ℝ → Set ℂ := fun c' d' => {ζ : ℂ | c' ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ d'} with hAnndef
  have hAnnmem : ∀ (c' d' : ℝ) (ζ : ℂ), ζ ∈ Ann c' d' ↔ (c' ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ d') := by
    intro c' d' ζ
    rw [hAnndef]
    exact Iff.rfl
  have hAnncomp : ∀ c' d' : ℝ, IsCompact (Ann c' d') := by
    intro c' d'
    rw [hAnndef]
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := d')).subset ?_
      intro ζ hζ
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hζ.2
  have hAnnsub : ∀ c' d' : ℝ, a < c' → d' < b → Ann c' d' ⊆ A := by
    intro c' d' h1 h2 ζ hζ
    rw [hAnnmem] at hζ
    exact (hAmem ζ).mpr ⟨lt_of_lt_of_le h1 hζ.1, lt_of_le_of_lt hζ.2 h2⟩
  have hAnnmeas : ∀ c' d' : ℝ, MeasurableSet (Ann c' d') :=
    fun c' d' => (hAnncomp c' d').measurableSet
  -- the two measure-theoretic properties of the Fourier coefficient on a compact
  -- annulus -- integrability in the radius, and `L¹`-continuity -- are
  -- `FourierCoefAnnulusRegularity`; the aliases keep the application shape used below
  have hgen := fun (c' d' : ℝ) (hc' : 0 < c') => (FourierCoefAnnulusRegularity n k c' d' hc').1
  have hFCconv := fun (c' d' : ℝ) (hc' : 0 < c') => (FourierCoefAnnulusRegularity n k c' d' hc').2
  -- an enclosing open annulus for any pair of radii in `(a, b)`
  have hencl : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, ∃ c' d' : ℝ,
      0 < c' ∧ a < c' ∧ d' < b ∧ Set.uIcc c d ⊆ Set.Ioo c' d' := by
    intro c hc d hd
    have h1 : a < min c d := lt_min hc.1 hd.1
    have h2 : max c d < b := max_lt hc.2 hd.2
    refine ⟨(a + min c d) / 2, (max c d + b) / 2, by linarith, by linarith, by linarith, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Icc (min c d) (max c d) := hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  -- conjunct (a)
  have hAconj : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b,
      IntegrableOn (FourierCoefOfH n (HRad H) k) (Set.uIcc c d) volume := by
    intro c hc d hd
    obtain ⟨c', d', hc'0, hac', hd'b, hsub⟩ := hencl c hc d hd
    exact ((hgen c' d' hc'0 (HRad H) hRadmeas
      (hintK (Ann c' d') (hAnnsub c' d' hac' hd'b) (hAnncomp c' d')).1).1).mono_set hsub
  -- the exhaustion of `(a, b)` by closed subintervals
  set cm : ℕ → ℝ := fun m => a + (b - a) / ((m : ℝ) + 2) with hcmdef
  set dm : ℕ → ℝ := fun m => b - (b - a) / ((m : ℝ) + 2) with hdmdef
  have hba : 0 < b - a := by linarith
  have hden : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 2 := by
    intro m
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hxnn : ∀ m : ℕ, 0 < (b - a) / ((m : ℝ) + 2) :=
    fun m => div_pos hba (hden m)
  have hcma : ∀ m, a < cm m := by
    intro m
    rw [hcmdef]
    simp only
    linarith [hxnn m]
  have hdmb : ∀ m, dm m < b := by
    intro m
    rw [hdmdef]
    simp only
    linarith [hxnn m]
  have hcmpos : ∀ m, 0 < cm m := fun m => lt_of_le_of_lt ha (hcma m)
  have hcmle : ∀ m, cm m ≤ dm m := by
    intro m
    rw [hcmdef, hdmdef]
    simp only
    have hx : (b - a) / ((m : ℝ) + 2) * ((m : ℝ) + 2) = b - a :=
      div_mul_cancel₀ _ (hden m).ne'
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hx, mul_nonneg (le_of_lt (hxnn m)) hm0]
  have hcmab : ∀ m, cm m ∈ Set.Ioo a b :=
    fun m => ⟨hcma m, lt_of_le_of_lt (hcmle m) (hdmb m)⟩
  have hdmab : ∀ m, dm m ∈ Set.Ioo a b :=
    fun m => ⟨lt_of_lt_of_le (hcma m) (hcmle m), hdmb m⟩
  have hIoosub : ∀ m, Set.Ioo (cm m) (dm m) ⊆ Set.Ioo a b :=
    fun m x hx => ⟨lt_trans (hcma m) hx.1, lt_trans hx.2 (hdmb m)⟩
  have hcover : ∀ r ∈ Set.Ioo a b, ∃ m : ℕ, r ∈ Set.Ioo (cm m) (dm m) := by
    intro r hr
    set ε : ℝ := min (r - a) (b - r) with hεdef
    have hε : 0 < ε := lt_min (by linarith [hr.1]) (by linarith [hr.2])
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (b - a) / ((m : ℝ) + 2) < ε := by
      refine ⟨⌈(b - a) / ε⌉₊, ?_⟩
      have h1 : (b - a) / ε ≤ ((⌈(b - a) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : (0 : ℝ) < ((⌈(b - a) / ε⌉₊ : ℕ) : ℝ) + 2 := hden _
      have h3 : (b - a) / ε * ε = b - a := div_mul_cancel₀ _ hε.ne'
      rw [div_lt_iff₀ h2]
      nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hε), h3, hε]
    refine ⟨m, ?_, ?_⟩
    · rw [hcmdef]
      simp only
      have h4 : ε ≤ r - a := min_le_left _ _
      linarith
    · rw [hdmdef]
      simp only
      have h4 : ε ≤ b - r := min_le_right _ _
      linarith
  -- conjunct (e)
  have hEconj : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
      (IntervalIntegrable (fun θ : ℝ => HRad H (ci r θ)) volume 0 (2 * Real.pi) ∧
        IntervalIntegrable (fun θ : ℝ => HAng H (ci r θ)) volume 0 (2 * Real.pi)) := by
    have hall : ∀ m : ℕ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (cm m) (dm m) →
        (IntervalIntegrable (fun θ : ℝ => HRad H (ci r θ)) volume 0 (2 * Real.pi) ∧
          IntervalIntegrable (fun θ : ℝ => HAng H (ci r θ)) volume 0 (2 * Real.pi)) := by
      intro m
      have hK := hintK (Ann (cm m) (dm m))
        (hAnnsub _ _ (hcma m) (hdmb m)) (hAnncomp _ _)
      have h1 := (hgen (cm m) (dm m) (hcmpos m) (HRad H) hRadmeas hK.1).2
      have h2 := (hgen (cm m) (dm m) (hcmpos m) (HAng H) hAngmeas hK.2).2
      filter_upwards [h1, h2] with r hr1 hr2 hr
      exact ⟨hr1 hr, hr2 hr⟩
    rw [← ae_all_iff] at hall
    filter_upwards [hall] with r hr hrab
    obtain ⟨m, hm⟩ := hcover r hrab
    exact hr m hm
  -- ===================================================================
  -- STEPS 3 and 4: the mollification and the transport of (H2) to it.
  -- ===================================================================
  set Lf : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hLfdef
  have hmollsmooth : ∀ W : Set ℂ, W ⊆ A → IsCompact W → ∀ φ : ContDiffBump (0 : ℂ),
      ContDiff ℝ (1 : ℕ) (convolution (W.indicator H) (φ.normed volume) Lf volume) := by
    intro W hWA hWc φ
    have hU : Integrable (W.indicator H) volume :=
      memLp_one_iff_integrable.mp (hH W hWA hWc)
    exact HasCompactSupport.contDiff_convolution_right (L := Lf)
      (hcg := φ.hasCompactSupport_normed) (hf := hU.locallyIntegrable)
      (hg := φ.contDiff_normed)
  have hmollfd : ∀ W : Set ℂ, W ⊆ A → IsCompact W → ∀ φ : ContDiffBump (0 : ℂ), ∀ x : ℂ,
      HasFDerivAt (convolution (W.indicator H) (φ.normed volume) Lf volume)
        (convolution (W.indicator H) (fderiv ℝ (φ.normed volume)) (Lf.precompR ℂ) volume x) x := by
    intro W hWA hWc φ x
    have hU : Integrable (W.indicator H) volume :=
      memLp_one_iff_integrable.mp (hH W hWA hWc)
    exact HasCompactSupport.hasFDerivAt_convolution_right
      (L := Lf) (hcg := φ.hasCompactSupport_normed) (hf := hU.locallyIntegrable)
      (hg := φ.contDiff_normed) x
  have hmollstep : ∀ W : Set ℂ, W ⊆ A → IsCompact W → ∀ φ : ContDiffBump (0 : ℂ),
      ∀ (j : Fin 2) (z : ℂ), (∀ w : ℂ, dist w z ≤ φ.rOut → w ∈ W) →
      (convolution (W.indicator H) (fderiv ℝ (φ.normed volume)) (Lf.precompR ℂ) volume z)
            (if j = 0 then 1 else Complex.I)
        = convolution (W.indicator (D j)) (φ.normed volume) Lf volume z := by
    intro W hWA hWc φ j z hmatch
    set ej : ℂ := if j = 0 then 1 else Complex.I with hejdef
    set U : ℂ → ℂ := W.indicator H with hUdef
    set V : ℂ → ℂ := W.indicator (D j) with hVdef
    have hU : Integrable U volume := by
      rw [hUdef]; exact memLp_one_iff_integrable.mp (hH W hWA hWc)
    have hV : Integrable V volume := by
      rw [hVdef]; exact memLp_one_iff_integrable.mp (hD j W hWA hWc)
    set ρ : ℂ → ℝ := φ.normed volume with hρdef
    have hρsmooth : ContDiff ℝ (⊤ : ℕ∞) ρ := φ.contDiff_normed
    have hρtsupp : tsupport ρ = Metric.closedBall (0 : ℂ) φ.rOut :=
      φ.tsupport_normed_eq
    -- (2d) the indicator-matching helper
    have hballdist : ∀ w : ℂ, z - w ∈ Metric.closedBall (0 : ℂ) φ.rOut →
        dist w z ≤ φ.rOut := by
      intro w hw
      simp only [Metric.mem_closedBall, dist_zero_right] at hw
      rw [dist_eq_norm, ← norm_neg]
      simpa using hw
    -- (2a) the test function
    set ψ : ℂ → ℂ := fun w => ((ρ (z - w) : ℝ) : ℂ) with hψdef
    have hψsupp : Function.support ψ ⊆ Metric.closedBall z φ.rOut := by
      intro w hw
      have hne : ρ (z - w) ≠ 0 := by
        simpa [hψdef, Complex.ofReal_eq_zero] using hw
      have hmem : z - w ∈ tsupport ρ := subset_tsupport ρ hne
      rw [hρtsupp] at hmem
      simpa [Metric.mem_closedBall] using hballdist w hmem
    have hψtsupp : tsupport ψ ⊆ Metric.closedBall z φ.rOut :=
      closure_minimal hψsupp Metric.isClosed_closedBall
    have hψtest : IsTestFn A ψ := by
      refine ⟨?_, ?_, ?_⟩
      · exact Complex.ofRealCLM.contDiff.comp
          (hρsmooth.comp (contDiff_const.sub contDiff_id))
      · exact HasCompactSupport.intro (isCompact_closedBall z φ.rOut)
          (fun x hx => Function.notMem_support.mp (fun hc => hx (hψsupp hc)))
      · intro w hw
        exact hWA (hmatch w (by simpa [Metric.mem_closedBall] using hψtsupp hw))
    -- (2b) the derivative of the test function
    have hψd : ∀ w : ℂ, fderiv ℝ ψ w ej = -((fderiv ℝ ρ (z - w) ej : ℝ) : ℂ) := by
      intro w
      have h1 : HasFDerivAt (fun w : ℂ => z - w) (-ContinuousLinearMap.id ℝ ℂ) w :=
        (hasFDerivAt_id w).const_sub z
      have h2 : HasFDerivAt ρ (fderiv ℝ ρ (z - w)) (z - w) :=
        (hρsmooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h3 : HasFDerivAt ψ
          (Complex.ofRealCLM.comp
            ((fderiv ℝ ρ (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ))) w :=
        Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp w h1)
      rw [h3.fderiv]
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg, Complex.ofRealCLM_apply]
    -- (2c) feed it to (H2)
    have hw := hweak j ψ hψtest
    rw [← hejdef] at hw
    simp_rw [hψd, hψdef, mul_neg] at hw
    rw [integral_neg, neg_inj] at hw
    -- hw : ∫ w, u w * ((fderiv ℝ ρ (z - w)) e : ℂ) = ∫ w, D w * ((ρ (z - w) : ℝ) : ℂ)
    -- (2d) replace `u`, `D` by their truncations, pointwise
    have hUmatch : ∀ w : ℂ, H w * (((fderiv ℝ ρ (z - w)) ej : ℝ) : ℂ)
        = ((fderiv ℝ ρ (z - w)) ej) • U w := by
      intro w
      by_cases hc : (fderiv ℝ ρ (z - w)) ej = 0
      · simp [hc]
      · have hne : fderiv ℝ ρ (z - w) ≠ 0 := by
          intro h0; rw [h0] at hc; simp at hc
        have hmem : z - w ∈ tsupport ρ :=
          (support_fderiv_subset ℝ) (Function.mem_support.mpr hne)
        rw [hρtsupp] at hmem
        have : U w = H w := by
          rw [hUdef, Set.indicator_of_mem (hmatch w (hballdist w hmem))]
        rw [this, Complex.real_smul, mul_comm]
    have hVmatch : ∀ w : ℂ, D j w * ((ρ (z - w) : ℝ) : ℂ) = (ρ (z - w)) • V w := by
      intro w
      by_cases hc : ρ (z - w) = 0
      · simp [hc]
      · have hmem : z - w ∈ tsupport ρ := subset_tsupport ρ hc
        rw [hρtsupp] at hmem
        have : V w = D j w := by
          rw [hVdef, Set.indicator_of_mem (hmatch w (hballdist w hmem))]
        rw [this, Complex.real_smul, mul_comm]
    simp_rw [hUmatch, hVmatch] at hw
    -- (2e) read both sides as convolutions
    have hUloc : LocallyIntegrable U volume := hU.locallyIntegrable
    rw [convolution_precompR_apply Lf hUloc
      (φ.hasCompactSupport_normed.fderiv ℝ)
      (hρsmooth.continuous_fderiv (by norm_num)) z ej]
    simp only [convolution_def, hLfdef, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply]
    exact hw
  -- STEP 5 (first half): the polar derivatives of the mollification
  have hmollpolar : ∀ W : Set ℂ, W ⊆ A → IsCompact W → ∀ φ : ContDiffBump (0 : ℂ),
      ∀ z : ℂ, z ≠ 0 → (∀ w : ℂ, dist w z ≤ φ.rOut → w ∈ W) →
      HRad (convolution (W.indicator H) (φ.normed volume) Lf volume) z
            = (z.re / ‖z‖) • convolution (W.indicator (D 0)) (φ.normed volume) Lf volume z
              + (z.im / ‖z‖) • convolution (W.indicator (D 1)) (φ.normed volume) Lf volume z
        ∧ HAng (convolution (W.indicator H) (φ.normed volume) Lf volume) z
            = (-z.im) • convolution (W.indicator (D 0)) (φ.normed volume) Lf volume z
              + z.re • convolution (W.indicator (D 1)) (φ.normed volume) Lf volume z := by
    intro W hWA hWc φ z hzne hmatch
    have hfd := (hmollfd W hWA hWc φ z).fderiv
    have h0 := hmollstep W hWA hWc φ 0 z hmatch
    have h1 := hmollstep W hWA hWc φ 1 z hmatch
    rw [if_pos rfl] at h0
    rw [if_neg (by decide : ¬((1 : Fin 2) = 0))] at h1
    constructor
    · rw [HRad, hfd]
      have hdec : z / ((‖z‖ : ℝ) : ℂ)
          = (z.re / ‖z‖) • (1 : ℂ) + (z.im / ‖z‖) • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        push_cast
        rw [div_mul_eq_mul_div, ← add_div]
        congr 1
        exact (Complex.re_add_im z).symm
      rw [hdec, map_add, map_smul, map_smul, h0, h1]
    · rw [HAng, hfd]
      have hdec : Complex.I * z = (-z.im) • (1 : ℂ) + z.re • Complex.I := by
        rw [Complex.real_smul, Complex.real_smul, mul_one]
        simp [Complex.ext_iff]
      rw [hdec, map_add, map_smul, map_smul, h0, h1]
  -- ===================================================================
  -- Generic one-variable calculus along rays and circles.
  -- ===================================================================
  have hRadmeasG : ∀ G : ℂ → ℂ, Measurable (HRad G) := fun G =>
    hev.measurable.comp ((measurable_fderiv ℝ G).prodMk hdivmeas)
  have hAngmeasG : ∀ G : ℂ → ℂ, Measurable (HAng G) := fun G =>
    hev.measurable.comp ((measurable_fderiv ℝ G).prodMk (by fun_prop))
  have hofR : ∀ x : ℝ, HasDerivAt (fun σ : ℝ => ((σ : ℝ) : ℂ)) 1 x := by
    intro x
    simpa [Complex.real_smul] using (hasDerivAt_id x).smul_const (1 : ℂ)
  have hcids : ∀ θ s : ℝ,
      HasDerivAt (fun σ : ℝ => ci σ θ) (Complex.exp ((θ : ℂ) * Complex.I)) s := by
    intro θ s
    simp only [hcidef]
    simpa using (hofR s).mul_const (Complex.exp ((θ : ℂ) * Complex.I))
  have hcidθ : ∀ r θ : ℝ, HasDerivAt (fun τ : ℝ => ci r τ) (Complex.I * ci r θ) θ := by
    intro r θ
    have hb : HasDerivAt (fun τ : ℝ => ((τ : ℝ) : ℂ) * Complex.I) Complex.I θ := by
      simpa using (hofR θ).mul_const Complex.I
    have hc : HasDerivAt (fun τ : ℝ => Complex.exp (((τ : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I) θ := hb.cexp
    have hd := hc.const_mul (((r : ℝ) : ℂ))
    have he : ((r : ℝ) : ℂ) * (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I)
        = Complex.I * ci r θ := by
      simp only [hcidef]
      ring
    rw [← he]
    simp only [hcidef]
    exact hd
  have hcinormdiv : ∀ s θ : ℝ, 0 < s →
      ci s θ / ((‖ci s θ‖ : ℝ) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    intro s θ hs
    have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    rw [hcinorm s θ, abs_of_pos hs]
    simp only [hcidef]
    field_simp
  have hRadci : ∀ (G : ℂ → ℂ) (s θ : ℝ), 0 < s →
      HRad G (ci s θ) = fderiv ℝ G (ci s θ) (Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro G s θ hs
    rw [HRad, hcinormdiv s θ hs]
  have hray : ∀ G : ℂ → ℂ, ContDiff ℝ (1 : ℕ) G → ∀ θ s : ℝ, 0 < s →
      HasDerivAt (fun σ : ℝ => G (ci σ θ)) (HRad G (ci s θ)) s := by
    intro G hG θ s hs
    have h2 : HasFDerivAt G (fderiv ℝ G (ci s θ)) (ci s θ) :=
      (hG.differentiable (by norm_num) (ci s θ)).hasFDerivAt
    have h3 := HasFDerivAt.comp_hasDerivAt (x := s) (hl := h2) (hf := hcids θ s)
    rw [hRadci G s θ hs]
    simpa [Function.comp_def] using h3
  have hangd : ∀ G : ℂ → ℂ, ContDiff ℝ (1 : ℕ) G → ∀ r θ : ℝ,
      HasDerivAt (fun τ : ℝ => G (ci r τ)) (HAng G (ci r θ)) θ := by
    intro G hG r θ
    have h2 : HasFDerivAt G (fderiv ℝ G (ci r θ)) (ci r θ) :=
      (hG.differentiable (by norm_num) (ci r θ)).hasFDerivAt
    have h3 := HasFDerivAt.comp_hasDerivAt (x := θ) (hl := h2) (hf := hcidθ r θ)
    rw [HAng]
    simpa [Function.comp_def] using h3
  have hwtd : ∀ θ : ℝ,
      HasDerivAt wt (((((n : ℤ) - k : ℤ) : ℂ) * Complex.I) * wt θ) θ := by
    intro θ
    have hb : HasDerivAt (fun τ : ℝ => (((n : ℤ) - k : ℤ) : ℂ) * ((τ : ℝ) : ℂ) * Complex.I)
        ((((n : ℤ) - k : ℤ) : ℂ) * Complex.I) θ := by
      simpa using ((hofR θ).const_mul ((((n : ℤ) - k : ℤ) : ℂ))).mul_const Complex.I
    have hc := hb.cexp
    have he : Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * ((θ : ℝ) : ℂ) * Complex.I)
        * ((((n : ℤ) - k : ℤ) : ℂ) * Complex.I)
        = ((((n : ℤ) - k : ℤ) : ℂ) * Complex.I) * wt θ := by
      simp only [hwtdef]
      ring
    rw [← he]
    simp only [hwtdef]
    exact hc
  -- STEP 8 for a `C¹` function: the angular integration by parts
  have hIBP : ∀ G : ℂ → ℂ, ContDiff ℝ (1 : ℕ) G → ∀ r : ℝ,
      FourierCoefOfH n (HAng G) k r
        = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n G k r := by
    intro G hG r
    set m : ℂ := (((n : ℤ) - k : ℤ) : ℂ) with hmdef
    have hud : ∀ θ : ℝ, HasDerivAt (fun τ : ℝ => G (ci r τ) * wt τ)
        (HAng G (ci r θ) * wt θ + G (ci r θ) * (m * Complex.I * wt θ)) θ := by
      intro θ
      exact (hangd G hG r θ).mul (hwtd θ)
    have hGc : Continuous (fun τ : ℝ => G (ci r τ)) :=
      (hG.continuous).comp ((hcicont.comp (continuous_const.prodMk continuous_id)))
    have hdGc : Continuous (fun τ : ℝ => HAng G (ci r τ)) := by
      have h1 : Continuous (fderiv ℝ G) := (contDiff_one_iff_fderiv.mp hG).2
      have h2 : Continuous (fun τ : ℝ => ((fderiv ℝ G (ci r τ)), Complex.I * ci r τ)) :=
        (h1.comp ((hcicont.comp (continuous_const.prodMk continuous_id)))).prodMk
          (continuous_const.mul ((hcicont.comp (continuous_const.prodMk continuous_id))))
      exact hev.comp h2
    have hcont : Continuous (fun τ : ℝ =>
        HAng G (ci r τ) * wt τ + G (ci r τ) * (m * Complex.I * wt τ)) :=
      (hdGc.mul hwtcont).add (hGc.mul (continuous_const.mul hwtcont))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun τ : ℝ => G (ci r τ) * wt τ) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun x _ => hud x) (hcont.intervalIntegrable _ _)
    have hper : G (ci r (2 * Real.pi)) * wt (2 * Real.pi) = G (ci r 0) * wt 0 := by
      have h1 := hperci r 0
      have h2 := hperwt 0
      rw [zero_add] at h1 h2
      rw [h1, h2]
    rw [hper, sub_self] at hFTC
    have hsplit : (∫ τ in (0 : ℝ)..(2 * Real.pi),
          (HAng G (ci r τ) * wt τ + G (ci r τ) * (m * Complex.I * wt τ)))
        = (∫ τ in (0 : ℝ)..(2 * Real.pi), HAng G (ci r τ) * wt τ)
          + ∫ τ in (0 : ℝ)..(2 * Real.pi), G (ci r τ) * (m * Complex.I * wt τ) :=
      intervalIntegral.integral_add
        ((hdGc.mul hwtcont).intervalIntegrable _ _)
        ((hGc.mul (continuous_const.mul hwtcont)).intervalIntegrable _ _)
    rw [hsplit] at hFTC
    have hpull : (∫ τ in (0 : ℝ)..(2 * Real.pi), G (ci r τ) * (m * Complex.I * wt τ))
        = (m * Complex.I) * ∫ τ in (0 : ℝ)..(2 * Real.pi), G (ci r τ) * wt τ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext τ
      ring
    rw [hpull] at hFTC
    have hmain : (∫ τ in (0 : ℝ)..(2 * Real.pi), HAng G (ci r τ) * wt τ)
        = -((m * Complex.I) * ∫ τ in (0 : ℝ)..(2 * Real.pi), G (ci r τ) * wt τ) := by
      linear_combination hFTC
    rw [hFC (HAng G) r, hFC G r, hmain, hmdef]
    push_cast
    ring
  -- ===================================================================
  -- STEPS 3 to 6 and STEP 8: the mollification argument on a closed
  -- subinterval, giving conjunct (b) there and conjunct (d) there.
  -- ===================================================================
  have hcore : ∀ c d δ : ℝ, 0 < δ → a < c - 3 * δ → d + 3 * δ < b → 0 < c - 3 * δ → c ≤ d →
      (FourierCoefOfH n H k d - FourierCoefOfH n H k c
          = ∫ s in c..d, FourierCoefOfH n (HRad H) k s)
        ∧ (∀ᵐ r : ℝ, r ∈ Set.Ioo c d →
            FourierCoefOfH n (HAng H) k r
              = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r) := by
    intro c d δ hδ hac hdb hc3 hcd
    have hcpos : 0 < c := by linarith
    have hdpos : 0 < d := by linarith
    set A2 : Set ℂ := Ann (c - 3 * δ) (d + 3 * δ) with hA2def
    set Ab : Set ℂ := Ann (c - δ) (d + δ) with hAbdef
    have hA2A : A2 ⊆ A := hAnnsub _ _ hac hdb
    have hA2c : IsCompact A2 := hAnncomp _ _
    have hAbA : Ab ⊆ A := hAnnsub _ _ (by linarith) (by linarith)
    have hAbc : IsCompact Ab := hAnncomp _ _
    have hAbm : MeasurableSet Ab := hAnnmeas _ _
    have hmatchAb : ∀ z ∈ Ab, ∀ w : ℂ, dist w z ≤ δ → w ∈ A2 := by
      intro z hz w hw
      rw [hAbdef, hAnnmem] at hz
      rw [hA2def, hAnnmem]
      rw [dist_eq_norm] at hw
      have h1 : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
      have h2 : ‖z‖ - ‖w‖ ≤ ‖w - z‖ := by
        rw [← norm_sub_rev z w]
        exact norm_sub_norm_le z w
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hcircAb : ∀ s θ : ℝ, c - δ ≤ s → s ≤ d + δ → ci s θ ∈ Ab := by
      intro s θ h1 h2
      rw [hAbdef, hAnnmem, hcinorm s θ, abs_of_pos (by linarith)]
      exact ⟨h1, h2⟩
    -- the mollifier family
    set ε : ℕ → ℝ := fun l => min δ (1 / ((l : ℝ) + 1)) with hεdef
    have hεpos : ∀ l, 0 < ε l := by
      intro l
      rw [hεdef]
      exact lt_min hδ (by positivity)
    have hεδ : ∀ l, ε l ≤ δ := by
      intro l
      rw [hεdef]
      exact min_le_left _ _
    have hε1 : ∀ l, ε l ≤ 1 := by
      intro l
      have h1 : ε l ≤ 1 / ((l : ℝ) + 1) := by
        rw [hεdef]
        exact min_le_right _ _
      have h2 : 1 / ((l : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h3 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        linarith
      linarith
    have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun l : ℕ => 1 / ((l : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun l => (hεpos l).le) (fun l => ?_) hone
      rw [hεdef]
      exact min_le_right _ _
    set φ : ℕ → ContDiffBump (0 : ℂ) := fun l =>
      { rIn := ε l / 2
        rOut := ε l
        rIn_pos := half_pos (hεpos l)
        rIn_lt_rOut := half_lt_self (hεpos l) } with hφdef
    have hrOut : ∀ l, (φ l).rOut = ε l := fun l => rfl
    set Hl : ℕ → ℂ → ℂ := fun l =>
      convolution (A2.indicator H) ((φ l).normed volume) Lf volume with hHldef
    set Wl : Fin 2 → ℕ → ℂ → ℂ := fun j l =>
      convolution (A2.indicator (D j)) ((φ l).normed volume) Lf volume with hWldef
    have hHlsm : ∀ l, ContDiff ℝ (1 : ℕ) (Hl l) := by
      intro l
      rw [hHldef]
      exact hmollsmooth A2 hA2A hA2c (φ l)
    have hpol : ∀ (l : ℕ), ∀ z ∈ Ab,
        HRad (Hl l) z = (z.re / ‖z‖) • Wl 0 l z + (z.im / ‖z‖) • Wl 1 l z
          ∧ HAng (Hl l) z = (-z.im) • Wl 0 l z + z.re • Wl 1 l z := by
      intro l z hz
      have hznorm : c - δ ≤ ‖z‖ := by
        rw [hAbdef, hAnnmem] at hz
        exact hz.1
      have hzne : z ≠ 0 := by
        intro h
        rw [h] at hznorm
        simp at hznorm
        linarith
      have hm : ∀ w : ℂ, dist w z ≤ (φ l).rOut → w ∈ A2 :=
        fun w hw => hmatchAb z hz w (le_trans hw (le_trans (le_of_eq (hrOut l)) (hεδ l)))
      have h := hmollpolar A2 hA2A hA2c (φ l) z hzne hm
      rw [hHldef, hWldef]
      exact h
    -- STEP 5: the one-dimensional FTC along each ray, and Fubini
    set gl : ℕ → ℝ → ℝ → ℂ := fun l s θ =>
      fderiv ℝ (Hl l) (ci s θ) (Complex.exp ((θ : ℂ) * Complex.I)) * wt θ with hgldef
    have hglcont : ∀ l : ℕ, Continuous (fun p : ℝ × ℝ => gl l p.1 p.2) := by
      intro l
      have h1 : Continuous (fderiv ℝ (Hl l)) := (contDiff_one_iff_fderiv.mp (hHlsm l)).2
      have h2 : Continuous (fun p : ℝ × ℝ =>
          ((fderiv ℝ (Hl l) (ci p.1 p.2)), Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I))) :=
        (h1.comp hcicont).prodMk (by fun_prop)
      rw [hgldef]
      exact (hev.comp h2).mul (hwtcont.comp continuous_snd)
    have hglray : ∀ (l : ℕ) (θ : ℝ),
        (∫ s in c..d, gl l s θ) = (Hl l (ci d θ) - Hl l (ci c θ)) * wt θ := by
      intro l θ
      have hderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt (fun σ : ℝ => Hl l (ci σ θ))
          (fderiv ℝ (Hl l) (ci x θ) (Complex.exp ((θ : ℂ) * Complex.I))) x := by
        intro x hx
        rw [Set.uIcc_of_le hcd] at hx
        have hxpos : 0 < x := lt_of_lt_of_le hcpos hx.1
        rw [← hRadci (Hl l) x θ hxpos]
        exact hray (Hl l) (hHlsm l) θ x hxpos
      have hcon : Continuous (fun s : ℝ =>
          fderiv ℝ (Hl l) (ci s θ) (Complex.exp ((θ : ℂ) * Complex.I))) := by
        have h1 : Continuous (fderiv ℝ (Hl l)) := (contDiff_one_iff_fderiv.mp (hHlsm l)).2
        exact hev.comp (((h1.comp (hcicont.comp
          (continuous_id.prodMk continuous_const)))).prodMk continuous_const)
      have hbase := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcon.intervalIntegrable _ _)
      rw [hgldef]
      simp only
      rw [intervalIntegral.integral_mul_const, hbase]
    -- Fubini, giving the radial identity for the mollification
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hHlcirc : ∀ (l : ℕ) (r : ℝ), Continuous (fun θ : ℝ => Hl l (ci r θ) * wt θ) :=
      fun l r => (((hHlsm l).continuous).comp
        (hcicont.comp (continuous_const.prodMk continuous_id))).mul hwtcont
    have hFTCl : ∀ l : ℕ, (∫ s in c..d, FourierCoefOfH n (HRad (Hl l)) k s)
        = FourierCoefOfH n (Hl l) k d - FourierCoefOfH n (Hl l) k c := by
      intro l
      haveI hfm1 : IsFiniteMeasure (volume.restrict (Set.Ioc c d)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
      haveI hfm2 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
      obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ Set.Icc c d ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
          ‖gl l p.1 p.2‖ ≤ M :=
        (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
          (hglcont l).continuousOn
      have hint : Integrable (fun p : ℝ × ℝ => gl l p.1 p.2)
          ((volume.restrict (Set.Ioc c d)).prod
            (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
        refine Integrable.mono' (integrable_const M) (hglcont l).aestronglyMeasurable ?_
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod,
          ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
        filter_upwards with p hp
        exact hM p ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩
      have hswap2 : (∫ s in Set.Ioc c d, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), gl l s θ)
          = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ∫ s in Set.Ioc c d, gl l s θ :=
        MeasureTheory.integral_integral_swap hint
      have hiv1 : (∫ s in c..d, ∫ θ in (0 : ℝ)..(2 * Real.pi), gl l s θ)
          = ∫ s in Set.Ioc c d, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), gl l s θ := by
        rw [intervalIntegral.integral_of_le hcd]
        refine setIntegral_congr_fun measurableSet_Ioc ?_
        intro s _
        exact intervalIntegral.integral_of_le h2π
      have hiv2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ s in c..d, gl l s θ)
          = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ∫ s in Set.Ioc c d, gl l s θ := by
        rw [intervalIntegral.integral_of_le h2π]
        refine setIntegral_congr_fun measurableSet_Ioc ?_
        intro θ _
        exact intervalIntegral.integral_of_le hcd
      calc (∫ s in c..d, FourierCoefOfH n (HRad (Hl l)) k s)
          = ∫ s in c..d, (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), gl l s θ := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            rw [Set.uIcc_of_le hcd] at hx
            have hxpos : 0 < x := lt_of_lt_of_le hcpos hx.1
            rw [hFC (HRad (Hl l)) x]
            congr 1
            refine intervalIntegral.integral_congr ?_
            intro θ _
            show HRad (Hl l) (ci x θ) * wt θ = gl l x θ
            rw [hgldef]
            simp only
            rw [hRadci (Hl l) x θ hxpos]
        _ = (1 / (2 * Real.pi) : ℂ) * ∫ s in c..d, ∫ θ in (0 : ℝ)..(2 * Real.pi), gl l s θ :=
            intervalIntegral.integral_const_mul _ _
        _ = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ s in c..d, gl l s θ := by
            rw [hiv1, hiv2, hswap2]
        _ = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (Hl l (ci d θ) - Hl l (ci c θ)) * wt θ := by
            congr 1
            refine intervalIntegral.integral_congr ?_
            intro θ _
            exact hglray l θ
        _ = FourierCoefOfH n (Hl l) k d - FourierCoefOfH n (Hl l) k c := by
            rw [hFC (Hl l) d, hFC (Hl l) c, ← mul_sub,
              ← intervalIntegral.integral_sub ((hHlcirc l d).intervalIntegrable _ _)
                ((hHlcirc l c).intervalIntegrable _ _)]
            congr 1
            refine intervalIntegral.integral_congr ?_
            intro θ _
            ring
    -- the flip bridge between the two convolution orientations
    have hflip : ∀ (l : ℕ) (f : ℂ → ℂ), convolution f ((φ l).normed volume) Lf volume
        = convolution ((φ l).normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      intro l f
      rw [hLfdef]
      exact convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
    -- STEP 6a: uniform convergence of the mollification on the collar
    have hUmeas : AEStronglyMeasurable (A2.indicator H) volume :=
      (memLp_one_iff_integrable.mp (hH A2 hA2A hA2c)).aestronglyMeasurable
    have hunif : ∀ η : ℝ, 0 < η →
        ∀ᶠ l in Filter.atTop, ∀ z ∈ Ab, dist (Hl l z) (H z) ≤ η := by
      intro η hη
      obtain ⟨ρ, hρ, hρH⟩ : ∃ ρ > 0, ∀ x ∈ A2, ∀ y ∈ A2, dist x y < ρ → dist (H x) (H y) < η :=
        Metric.uniformContinuousOn_iff.mp
          (hA2c.uniformContinuousOn_of_continuous (hcont.mono hA2A)) η hη
      filter_upwards [hε0.eventually (gt_mem_nhds hρ)] with l hl z hz
      have hzA2 : z ∈ A2 := hmatchAb z hz z (by simpa using hδ.le)
      have hball : ∀ x ∈ Metric.ball z (φ l).rOut,
          dist (A2.indicator H x) (A2.indicator H z) ≤ η := by
        intro x hx
        rw [Metric.mem_ball, hrOut] at hx
        have hxA2 : x ∈ A2 := hmatchAb z hz x (le_trans hx.le (hεδ l))
        rw [Set.indicator_of_mem hxA2, Set.indicator_of_mem hzA2]
        exact le_of_lt (hρH x hxA2 z hzA2 (lt_trans hx hl))
      have hres := ContDiffBump.dist_normed_convolution_le (φ := φ l) (μ := volume)
        hUmeas hball
      rw [Set.indicator_of_mem hzA2] at hres
      rw [hHldef]
      simp only
      rw [hflip l (A2.indicator H)]
      exact hres
    have hconstnormR : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one,
        show ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hHcirc : ∀ r : ℝ, c - δ ≤ r → r ≤ d + δ →
        Continuous (fun θ : ℝ => H (ci r θ) * wt θ) := by
      intro r h1 h2
      refine Continuous.mul ?_ hwtcont
      exact hcont.comp_continuous (hcicont.comp (continuous_const.prodMk continuous_id))
        (fun θ => hAbA (hcircAb r θ h1 h2))
    have hFCunif : ∀ η : ℝ, 0 < η → ∀ᶠ l in Filter.atTop, ∀ r : ℝ, c - δ ≤ r → r ≤ d + δ →
        ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ ≤ η := by
        intro η hη
        filter_upwards [hunif η hη] with l hl r h1 h2
        have hd : FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r
            = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
                (Hl l (ci r θ) - H (ci r θ)) * wt θ := by
          rw [hFC (Hl l) r, hFC H r, ← mul_sub,
            ← intervalIntegral.integral_sub ((hHlcirc l r).intervalIntegrable _ _)
              ((hHcirc r h1 h2).intervalIntegrable _ _)]
          congr 1
          refine intervalIntegral.integral_congr ?_
          intro θ _
          ring
        have hb : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), (Hl l (ci r θ) - H (ci r θ)) * wt θ‖
            ≤ η * |2 * Real.pi - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
          intro θ _
          rw [norm_mul, hwtnorm θ, mul_one, ← dist_eq_norm]
          exact hl (ci r θ) (hcircAb r θ h1 h2)
        rw [hd, norm_mul, hconstnormR]
        rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hb
        calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
              (Hl l (ci r θ) - H (ci r θ)) * wt θ‖
            ≤ 1 / (2 * Real.pi) * (η * (2 * Real.pi)) := by
              refine mul_le_mul_of_nonneg_left hb (by positivity)
          _ = η := by field_simp
    have hFClim : ∀ r : ℝ, c - δ ≤ r → r ≤ d + δ →
        Filter.Tendsto (fun l => FourierCoefOfH n (Hl l) k r) Filter.atTop
          (nhds (FourierCoefOfH n H k r)) := by
      intro r h1 h2
      have hzero : Filter.Tendsto
          (fun l => FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r)
          Filter.atTop (nhds 0) := by
        rw [NormedAddGroup.tendsto_nhds_zero]
        intro η hη
        filter_upwards [hFCunif (η / 2) (by linarith)] with l hl
        exact lt_of_le_of_lt (hl r h1 h2) (by linarith)
      have h3 := hzero.add_const (FourierCoefOfH n H k r)
      simpa using h3
    -- STEP 6b: the `L¹` convergence of the mollified derivatives
    have halgM : ∀ (A B M : ℝ) (X0 X1 Y0 Y1 : ℂ), |A| ≤ M → |B| ≤ M → 0 ≤ M →
        ‖(A • X0 + B • X1) - (A • Y0 + B • Y1)‖ ≤ M * (‖X0 - Y0‖ + ‖X1 - Y1‖) := by
      intro A B M X0 X1 Y0 Y1 hA hB hM
      have he : (A • X0 + B • X1) - (A • Y0 + B • Y1)
          = A • (X0 - Y0) + B • (X1 - Y1) := by
        simp only [smul_sub]
        abel
      rw [he]
      have h1 := mul_le_mul_of_nonneg_right hA (norm_nonneg (X0 - Y0))
      have h2 := mul_le_mul_of_nonneg_right hB (norm_nonneg (X1 - Y1))
      calc ‖A • (X0 - Y0) + B • (X1 - Y1)‖
          ≤ ‖A • (X0 - Y0)‖ + ‖B • (X1 - Y1)‖ := norm_add_le _ _
        _ = |A| * ‖X0 - Y0‖ + |B| * ‖X1 - Y1‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ M * (‖X0 - Y0‖ + ‖X1 - Y1‖) := by nlinarith
    have hVi : ∀ j : Fin 2, Integrable (A2.indicator (D j)) volume := fun j =>
      memLp_one_iff_integrable.mp (hD j A2 hA2A hA2c)
    have hWi : ∀ (j : Fin 2) (l : ℕ), Integrable (Wl j l) volume := by
      intro j l
      rw [hWldef]
      simp only
      rw [hflip l (A2.indicator (D j))]
      exact ((φ l).integrable_normed).integrable_convolution _ (hVi j)
    have hWconv : ∀ j : Fin 2,
        Filter.Tendsto (fun l => ∫ ζ, ‖Wl j l ζ - (A2.indicator (D j)) ζ‖)
          Filter.atTop (nhds 0) := by
      intro j
      have hrt : Filter.Tendsto (fun l => (φ l).rOut) Filter.atTop (nhds 0) := hε0
      have h := MollificationL1Convergence (A2.indicator (D j)) (hVi j) φ (fun l => hε1 l) hrt
      refine h.congr ?_
      intro l
      rw [hWldef]
      simp only
      rw [hflip l (A2.indicator (D j))]
    have hWsum : Filter.Tendsto
        (fun l => ∫ ζ, (‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
          + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖)) Filter.atTop (nhds 0) := by
      have h0 := hWconv 0
      have h1 := hWconv 1
      have hsp : ∀ l : ℕ, (∫ ζ, (‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
          + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖))
          = (∫ ζ, ‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖)
            + ∫ ζ, ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖ := by
        intro l
        exact integral_add (((hWi 0 l).sub (hVi 0)).norm) (((hWi 1 l).sub (hVi 1)).norm)
      have := h0.add h1
      rw [add_zero] at this
      exact this.congr fun l => (hsp l).symm
    have hWsumi : ∀ l : ℕ, Integrable (fun ζ : ℂ => ‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
        + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖) volume :=
      fun l => (((hWi 0 l).sub (hVi 0)).norm).add (((hWi 1 l).sub (hVi 1)).norm)
    -- integrability of the truncated polar derivatives
    have hRadHl : ∀ l : ℕ, Integrable (Ab.indicator (HRad (Hl l))) volume := by
      intro l
      refine (integrable_indicator_iff hAbm).mpr ?_
      have h1 : Continuous (fderiv ℝ (Hl l)) := (contDiff_one_iff_fderiv.mp (hHlsm l)).2
      refine ContinuousOn.integrableOn_compact hAbc ?_
      intro z hz
      have hznorm : c - δ ≤ ‖z‖ := by
        rw [hAbdef, hAnnmem] at hz
        exact hz.1
      have hzne : z ≠ 0 := by
        intro h
        rw [h] at hznorm
        simp at hznorm
        linarith
      refine ContinuousAt.continuousWithinAt ?_
      have h2 : ContinuousAt (fun ζ : ℂ => ((fderiv ℝ (Hl l) ζ), ζ / ((‖ζ‖ : ℝ) : ℂ))) z := by
        refine (h1.continuousAt).prodMk ?_
        exact ContinuousAt.div continuousAt_id
          (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
          (by simpa using hzne)
      exact hev.continuousAt.comp h2
    have hAngHl : ∀ l : ℕ, Integrable (Ab.indicator (HAng (Hl l))) volume := by
      intro l
      refine (integrable_indicator_iff hAbm).mpr ?_
      have h1 : Continuous (fderiv ℝ (Hl l)) := (contDiff_one_iff_fderiv.mp (hHlsm l)).2
      refine ContinuousOn.integrableOn_compact hAbc ?_
      refine Continuous.continuousOn ?_
      exact hev.comp (h1.prodMk (continuous_const.mul continuous_id))
    have hRadHi : Integrable (Ab.indicator (HRad H)) volume :=
      (integrable_indicator_iff hAbm).mpr (hintK Ab hAbA hAbc).1
    have hAngHi : Integrable (Ab.indicator (HAng H)) volume :=
      (integrable_indicator_iff hAbm).mpr (hintK Ab hAbA hAbc).2
    have hcoefRad : ∀ ζ ∈ Ab, |ζ.re / ‖ζ‖| ≤ 1 ∧ |ζ.im / ‖ζ‖| ≤ 1 := by
      intro ζ hζ
      have hznorm : c - δ ≤ ‖ζ‖ := by
        rw [hAbdef, hAnnmem] at hζ
        exact hζ.1
      have hpos : 0 < ‖ζ‖ := by linarith
      refine ⟨?_, ?_⟩
      · rw [abs_div, abs_norm, div_le_one hpos]
        exact Complex.abs_re_le_norm ζ
      · rw [abs_div, abs_norm, div_le_one hpos]
        exact Complex.abs_im_le_norm ζ
    have hcoefAng : ∀ ζ ∈ Ab, |(-ζ.im)| ≤ d + δ ∧ |ζ.re| ≤ d + δ := by
      intro ζ hζ
      have hznorm : ‖ζ‖ ≤ d + δ := by
        rw [hAbdef, hAnnmem] at hζ
        exact hζ.2
      refine ⟨?_, ?_⟩
      · rw [abs_neg]
        exact le_trans (Complex.abs_im_le_norm ζ) hznorm
      · exact le_trans (Complex.abs_re_le_norm ζ) hznorm
    have hpolL1 : ∀ (M : ℝ), 0 ≤ M → ∀ (P : (ℂ → ℂ) → ℂ → ℂ),
        (∀ l : ℕ, Integrable (Ab.indicator (P (Hl l))) volume) →
        Integrable (Ab.indicator (P H)) volume →
        (∀ᵐ ζ : ℂ, ∀ l : ℕ, ‖(Ab.indicator (P (Hl l))) ζ - (Ab.indicator (P H)) ζ‖
          ≤ M * (‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
            + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖)) →
        Filter.Tendsto (fun l => ∫ ζ, ‖(Ab.indicator (P (Hl l))) ζ
          - (Ab.indicator (P H)) ζ‖) Filter.atTop (nhds 0) := by
      intro M hM P hPi hPHi hpt
      have hub : ∀ l : ℕ, (∫ ζ, ‖(Ab.indicator (P (Hl l))) ζ - (Ab.indicator (P H)) ζ‖)
          ≤ M * ∫ ζ, (‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
            + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖) := by
        intro l
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ζ => norm_nonneg _)
          ((hWsumi l).const_mul M) ?_
        filter_upwards [hpt] with ζ hζ
        exact hζ l
      have hlb : ∀ l : ℕ, (0 : ℝ)
          ≤ ∫ ζ, ‖(Ab.indicator (P (Hl l))) ζ - (Ab.indicator (P H)) ζ‖ :=
        fun l => integral_nonneg fun ζ => norm_nonneg _
      have hMt : Filter.Tendsto (fun l => M * ∫ ζ, (‖Wl 0 l ζ - (A2.indicator (D 0)) ζ‖
          + ‖Wl 1 l ζ - (A2.indicator (D 1)) ζ‖)) Filter.atTop (nhds 0) := by
        have := hWsum.const_mul M
        rw [mul_zero] at this
        exact this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hMt
        (Filter.Eventually.of_forall hlb) (Filter.Eventually.of_forall hub)
    have hRadL1 : Filter.Tendsto (fun l => ∫ ζ, ‖(Ab.indicator (HRad (Hl l))) ζ
        - (Ab.indicator (HRad H)) ζ‖) Filter.atTop (nhds 0) := by
      refine hpolL1 1 zero_le_one (fun G => HRad G) hRadHl hRadHi ?_
      filter_upwards [hstep1] with ζ hζ l
      by_cases hmem : ζ ∈ Ab
      · have hA : ζ ∈ A := hAbA hmem
        have hA2 : ζ ∈ A2 := hmatchAb ζ hmem ζ (by simpa using hδ.le)
        simp only [Set.indicator_of_mem hmem]
        rw [(hpol l ζ hmem).1, (hζ hA).1]
        simp only [Set.indicator_of_mem hA2]
        exact halgM _ _ 1 _ _ _ _ (hcoefRad ζ hmem).1 (hcoefRad ζ hmem).2 zero_le_one
      · simp only [Set.indicator_of_notMem hmem]
        simp only [sub_zero, norm_zero, one_mul]
        positivity
    have hAngL1 : Filter.Tendsto (fun l => ∫ ζ, ‖(Ab.indicator (HAng (Hl l))) ζ
        - (Ab.indicator (HAng H)) ζ‖) Filter.atTop (nhds 0) := by
      refine hpolL1 (d + δ) (by linarith) (fun G => HAng G) hAngHl hAngHi ?_
      filter_upwards [hstep1] with ζ hζ l
      by_cases hmem : ζ ∈ Ab
      · have hA : ζ ∈ A := hAbA hmem
        have hA2 : ζ ∈ A2 := hmatchAb ζ hmem ζ (by simpa using hδ.le)
        simp only [Set.indicator_of_mem hmem]
        rw [(hpol l ζ hmem).2, (hζ hA).2]
        simp only [Set.indicator_of_mem hA2]
        exact halgM _ _ (d + δ) _ _ _ _ (hcoefAng ζ hmem).1 (hcoefAng ζ hmem).2 (by linarith)
      · simp only [Set.indicator_of_notMem hmem]
        simp only [sub_zero, norm_zero]
        positivity
    -- transfer between the truncated and the honest Fourier coefficients
    have hcδ : 0 < c - δ := by linarith
    have hFCind : ∀ (X : ℂ → ℂ) (r : ℝ), c - δ ≤ r → r ≤ d + δ →
        FourierCoefOfH n (Ab.indicator X) k r = FourierCoefOfH n X k r := by
      intro X r h1 h2
      rw [hFC (Ab.indicator X) r, hFC X r]
      congr 1
      refine intervalIntegral.integral_congr ?_
      intro θ _
      show Ab.indicator X (ci r θ) * wt θ = X (ci r θ) * wt θ
      rw [Set.indicator_of_mem (hcircAb r θ h1 h2)]
    have hIoosub2 : Set.Ioo c d ⊆ Set.Ioo (c - δ) (d + δ) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hIocsub : Set.Ioc c d ⊆ Set.Ioo (c - δ) (d + δ) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hIccsub : Set.uIcc c d ⊆ Set.Ioo (c - δ) (d + δ) := by
      rw [Set.uIcc_of_le hcd]
      exact fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFCIint : ∀ (W : ℂ → ℂ), Measurable W → Integrable W volume →
        IntegrableOn (FourierCoefOfH n W k) (Set.Ioo (c - δ) (d + δ)) volume :=
      fun W hWm hWi => (hgen (c - δ) (d + δ) hcδ W hWm hWi.integrableOn).1
    have hII : ∀ (W : ℂ → ℂ), Measurable W → Integrable W volume →
        IntervalIntegrable (FourierCoefOfH n W k) volume c d := by
      intro W hWm hWi
      rw [intervalIntegrable_iff]
      exact (hFCIint W hWm hWi).mono_set (le_trans Set.uIoc_subset_uIcc hIccsub)
    have hmono : volume.restrict (Set.Ioo c d) ≤ volume.restrict (Set.Ioo (c - δ) (d + δ)) :=
      Measure.restrict_mono hIoosub2 le_rfl
    have hmFC : ∀ (X : ℂ → ℂ), Measurable (Ab.indicator X) →
        Integrable (Ab.indicator X) volume →
        AEMeasurable (FourierCoefOfH n X k) (volume.restrict (Set.Ioo c d)) := by
      intro X hXm hXi
      have h1 : AEMeasurable (FourierCoefOfH n (Ab.indicator X) k)
          (volume.restrict (Set.Ioo c d)) :=
        ((hFCIint _ hXm hXi).aestronglyMeasurable.aemeasurable).mono_measure hmono
      refine h1.congr ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with r hr
      exact hFCind X r (by linarith [hr.1]) (by linarith [hr.2])
    have hHlAbm : ∀ l : ℕ, Measurable (Ab.indicator (Hl l)) :=
      fun l => ((hHlsm l).continuous.measurable).indicator hAbm
    have hHlAbi : ∀ l : ℕ, Integrable (Ab.indicator (Hl l)) volume := fun l =>
      (integrable_indicator_iff hAbm).mpr
        (ContinuousOn.integrableOn_compact hAbc ((hHlsm l).continuous.continuousOn))
    have hRadindm : ∀ l : ℕ, Measurable (Ab.indicator (HRad (Hl l))) :=
      fun l => (hRadmeasG (Hl l)).indicator hAbm
    have hAngindm : ∀ l : ℕ, Measurable (Ab.indicator (HAng (Hl l))) :=
      fun l => (hAngmeasG (Hl l)).indicator hAbm
    have hRadindmH : Measurable (Ab.indicator (HRad H)) := hRadmeas.indicator hAbm
    have hAngindmH : Measurable (Ab.indicator (HAng H)) := hAngmeas.indicator hAbm
    -- the real-valued bound on an interval integral coming from an `L¹` lintegral
    have hLtoR : ∀ Ps P : ℝ → ℂ,
        IntervalIntegrable Ps volume c d → IntervalIntegrable P volume c d →
        (∫⁻ s in Set.Ioo (c - δ) (d + δ), ‖Ps s - P s‖ₑ) ≠ ⊤ →
        ‖(∫ s in c..d, Ps s) - ∫ s in c..d, P s‖
          ≤ (∫⁻ s in Set.Ioo (c - δ) (d + δ), ‖Ps s - P s‖ₑ).toReal := by
      intro Ps P h1 h2 hfin
      rw [← intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_of_le hcd]
      have hb : ‖∫ s in Set.Ioc c d, (Ps s - P s)‖ₑ
          ≤ ∫⁻ s in Set.Ioo (c - δ) (d + δ), ‖Ps s - P s‖ₑ :=
        le_trans (enorm_integral_le_lintegral_enorm _)
          (lintegral_mono' (Measure.restrict_mono hIocsub le_rfl) le_rfl)
      rw [show ‖∫ s in Set.Ioc c d, (Ps s - P s)‖
          = (‖∫ s in Set.Ioc c d, (Ps s - P s)‖ₑ).toReal by
        rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]]
      exact ENNReal.toReal_mono hfin hb
    refine ⟨?_, ?_⟩
    · -- conjunct (b) on [c, d]
      have hconvR := hFCconv (c - δ) (d + δ) hcδ
        (fun l => Ab.indicator (HRad (Hl l))) (Ab.indicator (HRad H))
        hRadindm hRadindmH hRadHl hRadHi hRadL1
      have hfin : ∀ l : ℕ, (∫⁻ s in Set.Ioo (c - δ) (d + δ),
          ‖FourierCoefOfH n (Ab.indicator (HRad (Hl l))) k s
            - FourierCoefOfH n (Ab.indicator (HRad H)) k s‖ₑ) ≠ ⊤ :=
        fun l => (((hFCIint _ (hRadindm l) (hRadHl l)).sub
          (hFCIint _ hRadindmH hRadHi)).2).ne
      have hcongR : ∀ (X : ℂ → ℂ), (∫ s in c..d, FourierCoefOfH n (Ab.indicator X) k s)
          = ∫ s in c..d, FourierCoefOfH n X k s := by
        intro X
        refine intervalIntegral.integral_congr ?_
        intro x hx
        exact hFCind X x (by linarith [(hIccsub hx).1]) (by linarith [(hIccsub hx).2])
      have hlim2 : Filter.Tendsto (fun l => ∫ s in c..d, FourierCoefOfH n (HRad (Hl l)) k s)
          Filter.atTop (nhds (∫ s in c..d, FourierCoefOfH n (HRad H) k s)) := by
        have hz : Filter.Tendsto (fun l => (∫ s in c..d, FourierCoefOfH n (HRad (Hl l)) k s)
            - ∫ s in c..d, FourierCoefOfH n (HRad H) k s) Filter.atTop (nhds 0) := by
          refine squeeze_zero_norm' (Filter.Eventually.of_forall fun l => ?_)
            ((ENNReal.tendsto_toReal (by simp)).comp hconvR)
          rw [← hcongR (HRad (Hl l)), ← hcongR (HRad H)]
          exact hLtoR _ _ (hII _ (hRadindm l) (hRadHl l)) (hII _ hRadindmH hRadHi) (hfin l)
        have h3 := hz.add_const (∫ s in c..d, FourierCoefOfH n (HRad H) k s)
        simpa using h3
      have hlim1 : Filter.Tendsto (fun l => FourierCoefOfH n (Hl l) k d
          - FourierCoefOfH n (Hl l) k c) Filter.atTop
          (nhds (FourierCoefOfH n H k d - FourierCoefOfH n H k c)) :=
        (hFClim d (by linarith) (by linarith)).sub (hFClim c (by linarith) (by linarith))
      exact tendsto_nhds_unique (hlim1.congr fun l => (hFTCl l).symm) hlim2
    · -- conjunct (d) on (c, d)
      set C : ℂ := Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) with hCdef
      set Q : ℝ → ℂ := fun r => FourierCoefOfH n (HAng H) k r - C * FourierCoefOfH n H k r
        with hQdef
      have hmFCH : AEMeasurable (FourierCoefOfH n H k) (volume.restrict (Set.Ioo c d)) := by
        refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop
          (fun l => hmFC (Hl l) (hHlAbm l) (hHlAbi l)) ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards with r hr
        exact hFClim r (by linarith [hr.1]) (by linarith [hr.2])
      have hmFCAngH : AEMeasurable (FourierCoefOfH n (HAng H) k)
          (volume.restrict (Set.Ioo c d)) := hmFC (HAng H) hAngindmH hAngHi
      have hmFCAngHl : ∀ l : ℕ, AEMeasurable (FourierCoefOfH n (HAng (Hl l)) k)
          (volume.restrict (Set.Ioo c d)) :=
        fun l => hmFC (HAng (Hl l)) (hAngindm l) (hAngHl l)
      have hmQ : AEMeasurable (fun r => ‖Q r‖ₑ) (volume.restrict (Set.Ioo c d)) := by
        rw [hQdef]
        exact (hmFCAngH.sub (hmFCH.const_mul C)).enorm
      -- the second error term, from uniform convergence
      have hT2 : Filter.Tendsto (fun l => ∫⁻ r in Set.Ioo c d,
          ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ₑ) Filter.atTop (nhds 0) := by
        rw [ENNReal.tendsto_nhds_zero]
        intro ζ hζ
        rcases eq_or_ne ζ ⊤ with rfl | hζtop
        · exact Filter.Eventually.of_forall fun l => le_top
        · have hζR : 0 < ζ.toReal := ENNReal.toReal_pos hζ.ne' hζtop
          have hdc : 0 ≤ d - c := by linarith
          set η : ℝ := ζ.toReal / ((d - c) + 1) with hηdef
          have hη : 0 < η := by
            rw [hηdef]
            exact div_pos hζR (by linarith)
          filter_upwards [hFCunif η hη] with l hl
          have hpt : ∀ᵐ r ∂(volume.restrict (Set.Ioo c d)),
              ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ₑ
                ≤ ENNReal.ofReal η := by
            rw [ae_restrict_iff' measurableSet_Ioo]
            filter_upwards with r hr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal
              (hl r (by linarith [hr.1]) (by linarith [hr.2]))
          calc (∫⁻ r in Set.Ioo c d,
                ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ₑ)
              ≤ ∫⁻ _r in Set.Ioo c d, ENNReal.ofReal η := lintegral_mono_ae hpt
            _ = ENNReal.ofReal η * volume (Set.Ioo c d) := by rw [setLIntegral_const]
            _ = ENNReal.ofReal (η * (d - c)) := by
                rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hη.le]
            _ ≤ ζ := by
                rw [← ENNReal.ofReal_toReal hζtop]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
                nlinarith [hζR, hdc]
      have hT1 := hFCconv (c - δ) (d + δ) hcδ
        (fun l => Ab.indicator (HAng (Hl l))) (Ab.indicator (HAng H))
        hAngindm hAngindmH hAngHl hAngHi hAngL1
      have hQbnd : ∀ l : ℕ, (∫⁻ r in Set.Ioo c d, ‖Q r‖ₑ)
          ≤ (∫⁻ s in Set.Ioo (c - δ) (d + δ),
                ‖FourierCoefOfH n (Ab.indicator (HAng (Hl l))) k s
                  - FourierCoefOfH n (Ab.indicator (HAng H)) k s‖ₑ)
            + ‖C‖ₑ * ∫⁻ r in Set.Ioo c d,
                ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ₑ := by
        intro l
        have hptw : ∀ᵐ r ∂(volume.restrict (Set.Ioo c d)), ‖Q r‖ₑ
            ≤ ‖FourierCoefOfH n (HAng (Hl l)) k r - FourierCoefOfH n (HAng H) k r‖ₑ
              + ‖C‖ₑ * ‖FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r‖ₑ := by
          rw [ae_restrict_iff' measurableSet_Ioo]
          filter_upwards with r _
          have hib : FourierCoefOfH n (HAng (Hl l)) k r = C * FourierCoefOfH n (Hl l) k r := by
            rw [hCdef]
            exact hIBP (Hl l) (hHlsm l) r
          have hdec : Q r = -(FourierCoefOfH n (HAng (Hl l)) k r
              - FourierCoefOfH n (HAng H) k r)
            + C * (FourierCoefOfH n (Hl l) k r - FourierCoefOfH n H k r) := by
            rw [hQdef]
            simp only
            rw [hib]
            ring
          rw [hdec]
          refine le_trans (enorm_add_le _ _) ?_
          rw [enorm_neg, enorm_mul]
        refine le_trans (lintegral_mono_ae hptw) ?_
        have hm1 : AEMeasurable (fun r : ℝ =>
            ‖FourierCoefOfH n (HAng (Hl l)) k r - FourierCoefOfH n (HAng H) k r‖ₑ)
            (volume.restrict (Set.Ioo c d)) := ((hmFCAngHl l).sub hmFCAngH).enorm
        rw [lintegral_add_left' hm1]
        refine add_le_add ?_ ?_
        · refine le_trans (le_of_eq ?_) (lintegral_mono' (Measure.restrict_mono hIoosub2 le_rfl)
            (le_refl _))
          refine lintegral_congr_ae ?_
          rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
          filter_upwards with r hr
          rw [hFCind (HAng (Hl l)) r (by linarith [hr.1]) (by linarith [hr.2]),
            hFCind (HAng H) r (by linarith [hr.1]) (by linarith [hr.2])]
        · rw [lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
      have hzero : (∫⁻ r in Set.Ioo c d, ‖Q r‖ₑ) = 0 := by
        have h2 := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hT2 (Or.inr (by simp [enorm_ne_top]))
        rw [mul_zero] at h2
        have h3 := hT1.add h2
        rw [add_zero] at h3
        exact le_antisymm (ge_of_tendsto h3 (Filter.Eventually.of_forall hQbnd)) zero_le
      rw [lintegral_eq_zero_iff' hmQ] at hzero
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at hzero
      filter_upwards [hzero] with r hr hrIoo
      have h := hr hrIoo
      simp only [Pi.zero_apply, enorm_eq_zero] at h
      rw [hQdef] at h
      simp only at h
      rw [hCdef] at h
      linear_combination h



  -- the collar width available around a closed subinterval of `(a, b)`
  have hδchoice : ∀ c d : ℝ, c ∈ Set.Ioo a b → d ∈ Set.Ioo a b → c ≤ d →
      ∃ δ : ℝ, 0 < δ ∧ a < c - 3 * δ ∧ d + 3 * δ < b ∧ 0 < c - 3 * δ := by
    intro c d hc hd hcd
    have h1 : min ((c - a) / 6) ((b - d) / 6) ≤ (c - a) / 6 := min_le_left _ _
    have h2 : min ((c - a) / 6) ((b - d) / 6) ≤ (b - d) / 6 := min_le_right _ _
    refine ⟨min ((c - a) / 6) ((b - d) / 6),
      lt_min (by linarith [hc.1]) (by linarith [hd.2]), by linarith [hc.1],
      by linarith [hd.2], by linarith [hc.1]⟩
  -- conjunct (b): Steps 3-6, the mollification argument
  have hBconj : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b,
      FourierCoefOfH n H k d - FourierCoefOfH n H k c
        = ∫ s in c..d, FourierCoefOfH n (HRad H) k s := by
    intro c hc d hd
    rcases le_total c d with hcd | hdc
    · obtain ⟨δ, hδ, h1, h2, h3⟩ := hδchoice c d hc hd hcd
      exact (hcore c d δ hδ h1 h2 h3 hcd).1
    · obtain ⟨δ, hδ, h1, h2, h3⟩ := hδchoice d c hd hc hdc
      have h := (hcore d c δ hδ h1 h2 h3 hdc).1
      rw [intervalIntegral.integral_symm]
      linear_combination -h
  -- conjunct (c): Step 7, from (a) and (b) by the Lebesgue differentiation theorem
  have hCconj : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
      HasDerivAt (FourierCoefOfH n H k) (FourierCoefOfH n (HRad H) k r) r := by
    have hall : ∀ m : ℕ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (cm m) (dm m) →
        HasDerivAt (FourierCoefOfH n H k) (FourierCoefOfH n (HRad H) k r) r := by
      intro m
      have hii : IntervalIntegrable (FourierCoefOfH n (HRad H) k) volume (cm m) (dm m) := by
        rw [intervalIntegrable_iff]
        exact (hAconj (cm m) (hcmab m) (dm m) (hdmab m)).mono_set Set.uIoc_subset_uIcc
      filter_upwards [hii.ae_hasDerivAt_integral] with r hr hrIoo
      have hruIcc : r ∈ Set.uIcc (cm m) (dm m) := by
        rw [Set.uIcc_of_le (hcmle m)]
        exact ⟨le_of_lt hrIoo.1, le_of_lt hrIoo.2⟩
      have hd := hr hruIcc (cm m) Set.left_mem_uIcc
      have hd2 : HasDerivAt (fun x => FourierCoefOfH n H k (cm m) +
          ∫ t in (cm m)..x, FourierCoefOfH n (HRad H) k t)
          (FourierCoefOfH n (HRad H) k r) r :=
        HasDerivAt.const_add (FourierCoefOfH n H k (cm m)) hd
      refine hd2.congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (hIoosub m hrIoo)) ?_
      intro x hx
      have hBx := hBconj (cm m) (hcmab m) x hx
      show FourierCoefOfH n H k x
        = FourierCoefOfH n H k (cm m) + ∫ t in (cm m)..x, FourierCoefOfH n (HRad H) k t
      linear_combination hBx
    rw [← ae_all_iff] at hall
    filter_upwards [hall] with r hr hrab
    obtain ⟨m, hm⟩ := hcover r hrab
    exact hr m hm
  -- conjunct (d): Step 8, the angular integration by parts
  have hDconj : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
      FourierCoefOfH n (HAng H) k r
        = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r := by
    have hall : ∀ m : ℕ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (cm m) (dm m) →
        FourierCoefOfH n (HAng H) k r
          = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r := by
      intro m
      obtain ⟨δ, hδ, h1, h2, h3⟩ := hδchoice (cm m) (dm m) (hcmab m) (hdmab m) (hcmle m)
      exact (hcore (cm m) (dm m) δ hδ h1 h2 h3 (hcmle m)).2
    rw [← ae_all_iff] at hall
    filter_upwards [hall] with r hr hrab
    obtain ⟨m, hm⟩ := hcover r hrab
    exact hr m hm
  exact ⟨hAconj, hBconj, hCconj, hDconj, hEconj⟩
