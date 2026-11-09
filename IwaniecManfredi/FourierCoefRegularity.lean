import IwaniecManfredi.CircleAvgLocAbsCont
import IwaniecManfredi.MemWLocOn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open MeasureTheory

/-- The regularity of the Fourier coefficients of `H` on the unit disk, for a
merely `W^{1,2}` solution: continuity up to the centre, local absolute
continuity in `r` away from it with the radial coefficient as derivative, the
angular identity, the integrability in `θ` of the two polar derivatives on
almost every circle, and the `L²` expansion (29).

This is the paper's (31) and (32) with Section 3's `C^∞` standing assumption
removed.  The paper reads that assumption at exactly one place,
`paper.tex:265-266`, to get `a_k ∈ C[0,1) ∩ C^∞(0,1)`; `paper.tex:269`
justifies (32) from `H ∈ W^{1,2}(𝔹)` alone.  Here the `C[0,1)` half comes from
continuity, which the inverse of a quasiconformal homeomorphism has for
nothing, and the `C^∞(0,1)` half is *not* claimed: it is regained downstream
from the system (33), which is the paper's own route to it being differentiable
in the first place.  What this node contributes over the general circle-average
lemma is the passage from the disk to the punctured disk -- the `L²`-to-`L¹`
Hölder step and the restriction of the integration-by-parts identity -- the
statement for the whole family of `k` at once, and the two clauses, (a) and
(f), that concern the centre and the `L²` expansion. -/
theorem FourierCoefRegularity (n : ℕ) (H : ℂ → ℂ)
    (hc : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1})
    (hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H)
    (hdiff : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ) :
    (∀ k : ℤ, ContinuousOn (FourierCoefOfH n H k) (Set.Ico (0 : ℝ) 1)) ∧
    (∀ (k : ℤ), ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∀ d ∈ Set.Ioo (0 : ℝ) 1,
      IntegrableOn (FourierCoefOfH n (HRad H) k) (Set.uIcc c d) volume ∧
        FourierCoefOfH n H k d - FourierCoefOfH n H k c
          = ∫ s in c..d, FourierCoefOfH n (HRad H) k s) ∧
    (∀ k : ℤ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (FourierCoefOfH n H k) (FourierCoefOfH n (HRad H) k r) r) ∧
    (∀ k : ℤ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      FourierCoefOfH n (HAng H) k r
        = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r) ∧
    (∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      IntervalIntegrable
          (fun θ : ℝ => HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          volume 0 (2 * Real.pi) ∧
        IntervalIntegrable
          (fun θ : ℝ => HAng H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          volume 0 (2 * Real.pi)) ∧
    (∀ r ∈ Set.Ico (0 : ℝ) 1,
      Filter.Tendsto
        (fun N : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                FourierCoefOfH n H k r
                  * Complex.exp (((k - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
        Filter.atTop (nhds 0)) := by
  classical
  have hab : (0:ℝ) < 2*Real.pi := by positivity
  -- ## Notation: the circle map, the exponential family, and the ambient disk
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hnormcirc : ∀ (r θ : ℝ), ‖(r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)‖ = |r| := by
    intro r θ
    simp [Complex.norm_exp_ofReal_mul_I]
  have hmemB : ∀ (r θ : ℝ), |r| < 1 →
      ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro r θ hr
    show ‖(r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)‖ < 1
    rw [hnormcirc]; exact hr
  -- Step 1: joint continuity.  For every radius `r` with `|r| < 1` the circle
  -- `θ ↦ r e^{iθ}` lands in the disk, so `θ ↦ H(r e^{iθ})` is continuous.
  have hcircCont : ∀ r : ℝ, |r| < 1 →
      Continuous (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) := by
    intro r hr
    exact hc.comp_continuous (by fun_prop) (fun θ => hmemB r θ hr)
  -- ## (a): continuity of the coefficients on `[0,1)`
  have hpartA : ∀ k : ℤ, ContinuousOn (FourierCoefOfH n H k) (Set.Ico (0 : ℝ) 1) := by
    intro k
    have hwtnorm : ∀ θ : ℝ,
        ‖Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * (θ:ℂ) * Complex.I)‖ = 1 := by
      intro θ
      rw [Complex.norm_exp]
      have h : ((((n : ℤ) - k : ℤ) : ℂ) * (θ:ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [h, Real.exp_zero]
    intro r₀ hr₀
    obtain ⟨hr₀0, hr₀1⟩ := Set.mem_Ico.mp hr₀
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) ((r₀+1)/2)).exists_bound_of_continuousOn
      (hc.mono (by
        intro ξ hξ
        simp only [Metric.mem_closedBall, dist_zero_right] at hξ
        show ‖ξ‖ < 1
        linarith))
    have hkey : ContinuousWithinAt
        (fun r : ℝ => ∫ θ in (0:ℝ)..(2*Real.pi),
          H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
            * Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * (θ:ℂ) * Complex.I))
        (Set.Ico (0:ℝ) 1) r₀ := by
      have hmemself : ∀ᶠ r in nhdsWithin r₀ (Set.Ico (0:ℝ) 1), r ∈ Set.Ico (0:ℝ) 1 :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => hx)
      have hsmall : ∀ᶠ r in nhdsWithin r₀ (Set.Ico (0:ℝ) 1), r < (r₀+1)/2 :=
        Filter.eventually_of_mem (nhdsWithin_le_nhds (Iio_mem_nhds (by linarith)))
          (fun x hx => hx)
      apply intervalIntegral.continuousWithinAt_of_dominated_interval
        (bound := fun _ => C)
      · filter_upwards [hmemself] with r hr
        obtain ⟨h1, h2⟩ := Set.mem_Ico.mp hr
        have habs : |r| < 1 := by rw [abs_of_nonneg h1]; exact h2
        exact ((hcircCont r habs).mul (by fun_prop)).aestronglyMeasurable.restrict
      · filter_upwards [hmemself, hsmall] with r hr hrρ
        refine Filter.Eventually.of_forall (fun θ _ => ?_)
        obtain ⟨h1, _⟩ := Set.mem_Ico.mp hr
        rw [norm_mul, hwtnorm, mul_one]
        apply hC
        simp only [Metric.mem_closedBall, dist_zero_right]
        rw [hnormcirc, abs_of_nonneg h1]
        exact hrρ.le
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall (fun θ _ => ?_)
        refine ContinuousWithinAt.mul ?_ continuousWithinAt_const
        have h1 : ContinuousAt (fun r : ℝ => (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) r₀ := by
          fun_prop
        have hpt : ((r₀:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) ∈ {ξ : ℂ | ‖ξ‖ < 1} :=
          hmemB r₀ θ (by rw [abs_of_nonneg hr₀0]; exact hr₀1)
        have h2 : ContinuousAt (fun r : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) r₀ :=
          ContinuousAt.comp (hc.continuousAt (hBopen.mem_nhds hpt)) h1
        exact h2.continuousWithinAt
    have hrepr : (FourierCoefOfH n H k) = fun r : ℝ => (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0:ℝ)..(2*Real.pi),
          H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
            * Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * (θ:ℂ) * Complex.I) := rfl
    rw [hrepr]
    exact hkey.const_mul _
  -- ## Steps 3-4: the punctured disk, and (b), (c), (d), (e) from the circle lemma
  have hcircAvg : ∀ k : ℤ,
      (∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ d ∈ Set.Ioo (0:ℝ) 1,
          IntegrableOn (FourierCoefOfH n (HRad H) k) (Set.uIcc c d) volume) ∧
      (∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ d ∈ Set.Ioo (0:ℝ) 1,
          FourierCoefOfH n H k d - FourierCoefOfH n H k c
            = ∫ s in c..d, FourierCoefOfH n (HRad H) k s) ∧
      (∀ᵐ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 →
          HasDerivAt (FourierCoefOfH n H k) (FourierCoefOfH n (HRad H) k r) r) ∧
      (∀ᵐ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 →
          FourierCoefOfH n (HAng H) k r
            = Complex.I * ((k - (n : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r) ∧
      (∀ᵐ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 →
          IntervalIntegrable
              (fun θ : ℝ => HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              volume 0 (2 * Real.pi) ∧
            IntervalIntegrable
              (fun θ : ℝ => HAng H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              volume 0 (2 * Real.pi)) := by
    intro k
    obtain ⟨D, hD0, hDLp, hDweak⟩ := hw
    have hsub : {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} ⊆ {ξ : ℂ | ‖ξ‖ < 1} := by
      intro ξ hξ
      exact hξ.2
    -- the `L²`-to-`L¹` Hölder step on compact subsets of the punctured disk
    have hholder : ∀ g : ℂ → ℂ, MemLpLocOn 2 {ξ : ℂ | ‖ξ‖ < 1} g →
        MemLpLocOn 1 {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} g := by
      intro g hg K hKA hKcpt
      have h2 : MemLp (K.indicator g) 2 volume := hg K (hKA.trans hsub) hKcpt
      refine h2.mono_exponent_of_measure_support_ne_top (s := K) ?_ ?_ (by norm_num)
      · intro x hx
        exact Set.indicator_of_notMem hx g
      · exact (hKcpt.measure_lt_top).ne
    have hHH : MemLpLocOn 1 {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} H := by
      apply hholder
      have h := hDLp [] (by simp)
      rwa [hD0] at h
    have hDD : ∀ j : Fin 2,
        MemLpLocOn 1 {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} (fun z => D [j] z) := by
      intro j
      exact hholder _ (hDLp [j] (by simp))
    have hweak : ∀ j : Fin 2,
        IsWeakPartialOn {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} j H (fun z => D [j] z) := by
      intro j φ hφ
      have hφ' : IsTestFn {ξ : ℂ | ‖ξ‖ < 1} φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
      have h := hDweak [] j (by simp)
      rw [hD0] at h
      simpa using h φ hφ'
    have hcontA : ContinuousOn H {ξ : ℂ | (0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)} := hc.mono hsub
    have hdiffA : ∀ᵐ ξ : ℂ, ((0:ℝ) < ‖ξ‖ ∧ ‖ξ‖ < (1:ℝ)) → DifferentiableAt ℝ H ξ := by
      filter_upwards [hdiff] with ξ hξ h
      exact hξ h.2
    exact CircleAvgLocAbsCont n 0 1 le_rfl one_pos k H (fun j => fun z => D [j] z)
      hHH hDD hweak hcontA hdiffA
  -- ## Step 5: the `L²` expansion (29)
  -- The exponential family `e_m(θ) = e^{imθ}` and the Fourier coefficient of a
  -- function on `[0,2π]`, each introduced with its defining equation.
  obtain ⟨ee, heeval⟩ : ∃ g : ℤ → ℝ → ℂ,
      ∀ (m : ℤ) (θ : ℝ), g m θ = Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨cf, hcfval⟩ : ∃ c : (ℝ → ℂ) → ℤ → ℂ,
      ∀ (f : ℝ → ℂ) (m : ℤ), c f m
        = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0:ℝ)..(2*Real.pi), f θ * ee (-m) θ :=
    ⟨_, fun _ _ => rfl⟩
  have heefun : ∀ m : ℤ,
      ee m = fun θ : ℝ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) :=
    fun m => funext (heeval m)
  have heecont : ∀ m : ℤ, Continuous (ee m) := by
    intro m
    rw [heefun m]
    fun_prop
  have heemul : ∀ (i m : ℤ) (θ : ℝ), ee i θ * ee m θ = ee (i + m) θ := by
    intro i m θ
    rw [heeval, heeval, heeval, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heeconj : ∀ (m : ℤ) (θ : ℝ), (starRingEnd ℂ) (ee m θ) = ee (-m) θ := by
    intro m θ
    rw [heeval, heeval, ← Complex.exp_conj]
    congr 1
    simp
  -- orthogonality of the exponential family on `[0, 2π]`
  have heeortho : ∀ m : ℤ,
      (∫ θ in (0:ℝ)..(2*Real.pi), ee m θ) = if m = 0 then (2*Real.pi : ℂ) else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm; simp [heeval]
    · rw [if_neg hm]
      have hcne : ((m : ℂ) * Complex.I) ≠ 0 := by simp [hm]
      have h1 : (∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (((m : ℂ) * Complex.I) * (θ:ℂ)))
          = (Complex.exp (((m:ℂ) * Complex.I) * ((2*Real.pi : ℝ) : ℂ))
              - Complex.exp (((m:ℂ) * Complex.I) * ((0:ℝ) : ℂ))) / ((m : ℂ) * Complex.I) :=
        integral_exp_mul_complex hcne
      have h2 : (∫ θ in (0:ℝ)..(2*Real.pi), ee m θ)
          = ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (((m : ℂ) * Complex.I) * (θ:ℂ)) :=
        intervalIntegral.integral_congr (fun θ _ => by rw [heeval]; ring_nf)
      rw [h2, h1]
      have h3 : ((m:ℂ) * Complex.I) * ((2*Real.pi : ℝ) : ℂ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h3, Complex.exp_int_mul_two_pi_mul_I]
      simp
  -- conjugation commutes with the interval integral
  have hivconj : ∀ (F : ℝ → ℂ) (u v : ℝ),
      (∫ θ in u..v, (starRingEnd ℂ) (F θ)) = (starRingEnd ℂ) (∫ θ in u..v, F θ) := by
    intro F u v
    simp only [intervalIntegral, map_sub]
    rw [← integral_conj, ← integral_conj]
  -- the Fourier coefficients of a residual `f - Σ_{j ∈ s} b j e_j`
  have hresid : ∀ (f : ℝ → ℂ), Continuous f → ∀ (s : Finset ℤ) (b : ℤ → ℂ) (i : ℤ), i ∈ s →
      (∫ θ in (0:ℝ)..(2*Real.pi), (f θ - ∑ j ∈ s, b j * ee j θ) * ee (-i) θ)
        = (2*Real.pi : ℂ) * (cf f i - b i) := by
    intro f hf s b i hi
    have hint1 : IntervalIntegrable (fun θ => f θ * ee (-i) θ) volume 0 (2*Real.pi) :=
      (hf.mul (heecont (-i))).intervalIntegrable _ _
    have hintsum : IntervalIntegrable (fun θ => ∑ j ∈ s, b j * ee (j + -i) θ)
        volume 0 (2*Real.pi) :=
      (continuous_finsetSum s
        (fun j _ => continuous_const.mul (heecont (j + -i)))).intervalIntegrable _ _
    have hterms : ∀ j ∈ s, IntervalIntegrable (fun θ => b j * ee (j + -i) θ)
        volume 0 (2*Real.pi) :=
      fun j _ => (continuous_const.mul (heecont (j + -i))).intervalIntegrable _ _
    have hpt : ∀ θ : ℝ, (f θ - ∑ j ∈ s, b j * ee j θ) * ee (-i) θ
        = f θ * ee (-i) θ - ∑ j ∈ s, b j * ee (j + -i) θ := by
      intro θ
      rw [sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_assoc, heemul]
    have hcfi : (∫ θ in (0:ℝ)..(2*Real.pi), f θ * ee (-i) θ) = (2*Real.pi : ℂ) * cf f i := by
      rw [hcfval]
      have hpine : (2 * (Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
      field_simp
    calc (∫ θ in (0:ℝ)..(2*Real.pi), (f θ - ∑ j ∈ s, b j * ee j θ) * ee (-i) θ)
        = ∫ θ in (0:ℝ)..(2*Real.pi), (f θ * ee (-i) θ - ∑ j ∈ s, b j * ee (j + -i) θ) :=
          intervalIntegral.integral_congr (fun θ _ => hpt θ)
      _ = (∫ θ in (0:ℝ)..(2*Real.pi), f θ * ee (-i) θ)
            - ∫ θ in (0:ℝ)..(2*Real.pi), ∑ j ∈ s, b j * ee (j + -i) θ :=
          intervalIntegral.integral_sub hint1 hintsum
      _ = (2*Real.pi : ℂ) * cf f i
            - ∑ j ∈ s, b j * (∫ θ in (0:ℝ)..(2*Real.pi), ee (j + -i) θ) := by
          rw [hcfi, intervalIntegral.integral_finsetSum hterms]
          congr 1
          exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
      _ = (2*Real.pi : ℂ) * (cf f i - b i) := by
          have hsum : ∑ j ∈ s, b j * (∫ θ in (0:ℝ)..(2*Real.pi), ee (j + -i) θ)
              = (2*Real.pi : ℂ) * b i := by
            rw [Finset.sum_congr rfl (fun j (_ : j ∈ s) =>
              by rw [heeortho (j + -i)] :
                ∀ j ∈ s, b j * (∫ θ in (0:ℝ)..(2*Real.pi), ee (j + -i) θ)
                  = b j * (if j + -i = 0 then (2*Real.pi : ℂ) else 0))]
            rw [Finset.sum_eq_single i]
            · simp [mul_comm]
            · intro j _ hji
              have hne0 : j + -i ≠ 0 := by omega
              simp [hne0]
            · intro h; exact absurd hi h
          rw [hsum]; ring
  -- the Pythagoras identity for a residual orthogonal to the window
  have hpythag : ∀ (R : ℝ → ℂ), Continuous R → ∀ (s : Finset ℤ) (c : ℤ → ℂ),
      (∀ j ∈ s, (∫ θ in (0:ℝ)..(2*Real.pi), R θ * ee (-j) θ) = 0) →
      (∫ θ in (0:ℝ)..(2*Real.pi), ‖R θ + ∑ j ∈ s, c j * ee j θ‖^2)
        = (∫ θ in (0:ℝ)..(2*Real.pi), ‖R θ‖^2)
          + ∫ θ in (0:ℝ)..(2*Real.pi), ‖∑ j ∈ s, c j * ee j θ‖^2 := by
    intro R hR s c h0
    have hD : Continuous (fun θ : ℝ => ∑ j ∈ s, c j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    set D : ℝ → ℂ := fun θ => ∑ j ∈ s, c j * ee j θ with hDdef
    have hcross1 : (∫ θ in (0:ℝ)..(2*Real.pi), R θ * (starRingEnd ℂ) (D θ)) = 0 := by
      have hpt : ∀ θ : ℝ, R θ * (starRingEnd ℂ) (D θ)
          = ∑ j ∈ s, (starRingEnd ℂ) (c j) * (R θ * ee (-j) θ) := by
        intro θ
        rw [hDdef]
        simp only [map_sum, map_mul, heeconj]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hterms : ∀ j ∈ s, IntervalIntegrable
          (fun θ => (starRingEnd ℂ) (c j) * (R θ * ee (-j) θ)) volume 0 (2*Real.pi) :=
        fun j _ => (continuous_const.mul (hR.mul (heecont (-j)))).intervalIntegrable _ _
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_finsetSum hterms]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [intervalIntegral.integral_const_mul, h0 j hj, mul_zero]
    have hcross2 : (∫ θ in (0:ℝ)..(2*Real.pi), D θ * (starRingEnd ℂ) (R θ)) = 0 := by
      have h := hivconj (fun θ => R θ * (starRingEnd ℂ) (D θ)) 0 (2*Real.pi)
      rw [hcross1, map_zero] at h
      rw [← h]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [map_mul, Complex.conj_conj]
      ring
    have hsq : ∀ z : ℂ, ((‖z‖^2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
      intro z
      rw [Complex.ofReal_pow]
      exact (RCLike.mul_conj z).symm
    have hintRR : IntervalIntegrable (fun θ => R θ * (starRingEnd ℂ) (R θ))
        volume 0 (2*Real.pi) :=
      (hR.mul (Complex.continuous_conj.comp hR)).intervalIntegrable _ _
    have hintDD : IntervalIntegrable (fun θ => D θ * (starRingEnd ℂ) (D θ))
        volume 0 (2*Real.pi) :=
      (hD.mul (Complex.continuous_conj.comp hD)).intervalIntegrable _ _
    have hintRD : IntervalIntegrable (fun θ => R θ * (starRingEnd ℂ) (D θ))
        volume 0 (2*Real.pi) :=
      (hR.mul (Complex.continuous_conj.comp hD)).intervalIntegrable _ _
    have hintDR : IntervalIntegrable (fun θ => D θ * (starRingEnd ℂ) (R θ))
        volume 0 (2*Real.pi) :=
      (hD.mul (Complex.continuous_conj.comp hR)).intervalIntegrable _ _
    have hmain : ((∫ θ in (0:ℝ)..(2*Real.pi), ‖R θ + D θ‖^2 : ℝ) : ℂ)
        = ((∫ θ in (0:ℝ)..(2*Real.pi), ‖R θ‖^2 : ℝ) : ℂ)
          + ((∫ θ in (0:ℝ)..(2*Real.pi), ‖D θ‖^2 : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
        ← intervalIntegral.integral_ofReal]
      have hpt : ∀ θ : ℝ, ((‖R θ + D θ‖^2 : ℝ) : ℂ)
          = ((R θ * (starRingEnd ℂ) (R θ)) + (D θ * (starRingEnd ℂ) (D θ)))
            + ((R θ * (starRingEnd ℂ) (D θ)) + (D θ * (starRingEnd ℂ) (R θ))) := by
        intro θ
        rw [hsq, map_add]
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
      rw [intervalIntegral.integral_add (hintRR.add hintDD) (hintRD.add hintDR),
        intervalIntegral.integral_add hintRR hintDD,
        intervalIntegral.integral_add hintRD hintDR, hcross1, hcross2]
      rw [intervalIntegral.integral_congr
          (fun θ (_ : θ ∈ Set.uIcc (0:ℝ) (2*Real.pi)) => hsq (R θ)),
        intervalIntegral.integral_congr
          (fun θ (_ : θ ∈ Set.uIcc (0:ℝ) (2*Real.pi)) => hsq (D θ))]
      ring
    exact_mod_cast hmain
  -- extending a trigonometric sum to a larger window by zero coefficients
  have hextee : ∀ (s t : Finset ℤ), s ⊆ t → ∀ (b : ℤ → ℂ) (θ : ℝ),
      ∑ j ∈ t, (if j ∈ s then b j else 0) * ee j θ = ∑ j ∈ s, b j * ee j θ := by
    intro s t hst b θ
    rw [← Finset.sum_subset hst]
    · exact Finset.sum_congr rfl (fun j hj => by rw [if_pos hj])
    · intro x _ hxs
      rw [if_neg hxs, zero_mul]
  -- the Fourier partial sum is the best `L²` approximation from its own window
  have hbest : ∀ (f : ℝ → ℂ), Continuous f → ∀ (s : Finset ℤ) (b : ℤ → ℂ),
      (∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - ∑ j ∈ s, cf f j * ee j θ‖^2)
        ≤ ∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - ∑ j ∈ s, b j * ee j θ‖^2 := by
    intro f hf s b
    have hsumc : Continuous (fun θ : ℝ => ∑ j ∈ s, cf f j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    have hR : Continuous (fun θ : ℝ => f θ - ∑ j ∈ s, cf f j * ee j θ) := hf.sub hsumc
    have h0 : ∀ j ∈ s,
        (∫ θ in (0:ℝ)..(2*Real.pi), (f θ - ∑ i ∈ s, cf f i * ee i θ) * ee (-j) θ) = 0 := by
      intro j hj
      rw [hresid f hf s (cf f) j hj, sub_self, mul_zero]
    have hpt : ∀ θ : ℝ, f θ - ∑ j ∈ s, b j * ee j θ
        = (f θ - ∑ j ∈ s, cf f j * ee j θ) + ∑ j ∈ s, (cf f j - b j) * ee j θ := by
      intro θ
      have hs : ∑ j ∈ s, (cf f j - b j) * ee j θ
          = (∑ j ∈ s, cf f j * ee j θ) - ∑ j ∈ s, b j * ee j θ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hs]; ring
    have hRHS : (∫ θ in (0:ℝ)..(2*Real.pi), ‖f θ - ∑ j ∈ s, b j * ee j θ‖^2)
        = ∫ θ in (0:ℝ)..(2*Real.pi),
            ‖(f θ - ∑ j ∈ s, cf f j * ee j θ) + ∑ j ∈ s, (cf f j - b j) * ee j θ‖^2 :=
      intervalIntegral.integral_congr (fun θ _ => by rw [hpt θ])
    rw [hRHS, hpythag _ hR s (fun j => cf f j - b j) h0]
    have hnn : 0 ≤ ∫ θ in (0:ℝ)..(2*Real.pi), ‖∑ j ∈ s, (cf f j - b j) * ee j θ‖^2 :=
      intervalIntegral.integral_nonneg (by positivity) (fun u _ => by positivity)
    linarith
  -- uniform approximation on the unit circle by trigonometric (Laurent) polynomials,
  -- by the Stone--Weierstrass theorem
  have htrig : ∀ (g : ℂ → ℂ), ContinuousOn g (Metric.sphere (0:ℂ) 1) → ∀ ε : ℝ, 0 < ε →
      ∃ (s : Finset ℤ) (b : ℤ → ℂ), ∀ w : ℂ, ‖w‖ = 1 →
        ‖g w - ∑ j ∈ s, b j * w ^ j‖ ≤ ε := by
    intro g hg ε hε
    have hnorm1 : ∀ w : ↥(Metric.sphere (0:ℂ) 1), ‖(w : ℂ)‖ = 1 := by
      intro w
      simp
    have hne : ∀ w : ↥(Metric.sphere (0:ℂ) 1), ((w : ℂ)) ≠ 0 := by
      intro w h
      have hw := hnorm1 w
      rw [h] at hw; simp at hw
    set mono : ℤ → C(↥(Metric.sphere (0:ℂ) 1), ℂ) := fun m => ⟨fun w => (w : ℂ) ^ m, by
      exact Continuous.zpow₀ continuous_subtype_val m (fun w => Or.inl (hne w))⟩ with hmonodef
    have hmono_apply : ∀ (m : ℤ) (w : ↥(Metric.sphere (0:ℂ) 1)), mono m w = (w : ℂ) ^ m :=
      fun _ _ => rfl
    have hmono_zero : mono 0 = 1 := by
      ext w; simp [hmono_apply]
    have hmono_add : ∀ a b : ℤ, mono (a + b) = mono a * mono b := by
      intro a b; ext w; simp [hmono_apply, zpow_add₀ (hne w)]
    have hmono_star : ∀ m : ℤ, star (mono m) = mono (-m) := by
      intro m; ext w
      have h1 := hnorm1 w
      have h2 : (starRingEnd ℂ) (w : ℂ) = ((w : ℂ))⁻¹ := by
        have hmc : (w : ℂ) * (starRingEnd ℂ) (w : ℂ) = 1 := by
          rw [RCLike.mul_conj, h1]; norm_num
        exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmc)
      simp only [ContinuousMap.star_apply, hmono_apply]
      rw [← starRingEnd_apply, map_zpow₀, h2, inv_zpow']
    have hext : ∀ (s t : Finset ℤ), s ⊆ t → ∀ (b : ℤ → ℂ) (w : ℂ),
        ∑ j ∈ t, (if j ∈ s then b j else 0) * w ^ j = ∑ j ∈ s, b j * w ^ j := by
      intro s t hst b w
      rw [← Finset.sum_subset hst]
      · exact Finset.sum_congr rfl (fun j hj => by rw [if_pos hj])
      · intro x _ hxs
        rw [if_neg hxs, zero_mul]
    set A : StarSubalgebra ℂ C(↥(Metric.sphere (0:ℂ) 1), ℂ) :=
      { toSubalgebra := Algebra.adjoin ℂ (Set.range mono)
        star_mem' := by
          change Algebra.adjoin ℂ (Set.range mono) ≤ star (Algebra.adjoin ℂ (Set.range mono))
          refine Algebra.adjoin_le ?_
          rintro - ⟨m, rfl⟩
          exact Algebra.subset_adjoin ⟨-m, (hmono_star m).symm⟩ } with hAdef
    have hAcoe : Subalgebra.toSubmodule A.toSubalgebra = Submodule.span ℂ (Set.range mono) := by
      rw [hAdef]
      apply Algebra.adjoin_eq_span_of_subset
      refine Set.Subset.trans ?_ Submodule.subset_span
      intro x hx
      refine Submonoid.closure_induction (fun _ => id) ⟨0, hmono_zero⟩ ?_ hx
      rintro - - - - ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, hmono_add a b⟩
    have hAsep : A.SeparatesPoints := by
      intro x y hxy
      refine ⟨_, ⟨mono 1, ?_, rfl⟩, ?_⟩
      · rw [hAdef]; exact Algebra.subset_adjoin ⟨1, rfl⟩
      · dsimp only
        rw [hmono_apply, hmono_apply, zpow_one, zpow_one]
        exact fun h => hxy (Subtype.coe_injective h)
    have hAtop : A.topologicalClosure = ⊤ :=
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hAsep
    have hApoly : ∀ x : C(↥(Metric.sphere (0:ℂ) 1), ℂ), x ∈ A →
        ∃ (s : Finset ℤ) (b : ℤ → ℂ), ∀ w : ↥(Metric.sphere (0:ℂ) 1),
          x w = ∑ j ∈ s, b j * (w : ℂ) ^ j := by
      intro x hx
      have hx' : x ∈ Submodule.span ℂ (Set.range mono) := by rw [← hAcoe]; exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨m, rfl⟩ := hy
          exact ⟨{m}, fun _ => 1, fun w => by simp [hmono_apply]⟩
      | zero => exact ⟨∅, fun _ => 0, fun w => by simp⟩
      | add y z hy hz ihy ihz =>
          obtain ⟨s₁, b₁, h₁⟩ := ihy
          obtain ⟨s₂, b₂, h₂⟩ := ihz
          refine ⟨s₁ ∪ s₂,
            fun j => (if j ∈ s₁ then b₁ j else 0) + (if j ∈ s₂ then b₂ j else 0), ?_⟩
          intro w
          rw [ContinuousMap.add_apply, h₁ w, h₂ w]
          rw [← hext s₁ (s₁ ∪ s₂) Finset.subset_union_left b₁ (w : ℂ),
            ← hext s₂ (s₁ ∪ s₂) Finset.subset_union_right b₂ (w : ℂ),
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      | smul a y hy ihy =>
          obtain ⟨s, b, h⟩ := ihy
          refine ⟨s, fun j => a * b j, ?_⟩
          intro w
          rw [ContinuousMap.smul_apply, h w, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
    have hGmem : (⟨Set.domRestrict (Metric.sphere (0:ℂ) 1) g, hg.domRestrict⟩ :
        C(↥(Metric.sphere (0:ℂ) 1), ℂ))
          ∈ closure (A : Set C(↥(Metric.sphere (0:ℂ) 1), ℂ)) := by
      have h : (⟨Set.domRestrict (Metric.sphere (0:ℂ) 1) g, hg.domRestrict⟩ :
          C(↥(Metric.sphere (0:ℂ) 1), ℂ)) ∈ A.topologicalClosure := by
        rw [hAtop]; exact StarSubalgebra.mem_top
      exact h
    obtain ⟨P, hPA, hPdist⟩ := Metric.mem_closure_iff.mp hGmem ε hε
    obtain ⟨s, b, hsb⟩ := hApoly P hPA
    refine ⟨s, b, ?_⟩
    intro w hw
    have hwZ : w ∈ Metric.sphere (0:ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hle := ContinuousMap.dist_apply_le_dist
      (f := (⟨Set.domRestrict (Metric.sphere (0:ℂ) 1) g, hg.domRestrict⟩ :
        C(↥(Metric.sphere (0:ℂ) 1), ℂ))) (g := P) (⟨w, hwZ⟩ : ↥(Metric.sphere (0:ℂ) 1))
    rw [dist_eq_norm] at hle
    have hPval : P (⟨w, hwZ⟩ : ↥(Metric.sphere (0:ℂ) 1)) = ∑ j ∈ s, b j * w ^ j := hsb _
    rw [hPval] at hle
    exact le_trans hle hPdist.le
  -- ## (f): the `L²` expansion (29) on every circle of radius `r ∈ [0,1)`
  have hpartF : ∀ r ∈ Set.Ico (0 : ℝ) 1,
      Filter.Tendsto
        (fun N : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                FourierCoefOfH n H k r
                  * Complex.exp (((k - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
        Filter.atTop (nhds 0) := by
    intro r hr
    obtain ⟨hr0, hr1⟩ := Set.mem_Ico.mp hr
    have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
    have hfcont : Continuous (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) :=
      hcircCont r habs
    have hzpow : ∀ (j : ℤ) (θ : ℝ), (Complex.exp ((θ:ℂ) * Complex.I)) ^ j = ee j θ := by
      intro j θ
      rw [heeval, ← Complex.exp_int_mul]
      congr 1
      ring
    have hcid : ∀ m : ℤ,
        cf (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) m
          = FourierCoefOfH n H (m + (n:ℤ)) r := by
      intro m
      rw [hcfval]
      unfold FourierCoefOfH
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [heeval]
      congr 2
      push_cast
      ring
    have hwin : ∀ (N : ℕ) (θ : ℝ),
        (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), FourierCoefOfH n H k r
            * Complex.exp (((k - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
          = ∑ m ∈ Finset.Icc (-(N : ℤ) - (n:ℤ)) ((N : ℤ) - (n:ℤ)),
              cf (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) m * ee m θ := by
      intro N θ
      refine Finset.sum_nbij' (fun x => x - (n:ℤ)) (fun x => x + (n:ℤ)) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        omega
      · intro a _; ring
      · intro a _; ring
      · intro a _
        have h1 : a - (n:ℤ) + (n:ℤ) = a := by omega
        rw [hcid, h1, heeval]
    have hgcont : ContinuousOn (fun w : ℂ => H ((r:ℂ) * w)) (Metric.sphere (0:ℂ) 1) := by
      refine hc.comp (by fun_prop) ?_
      intro w hw
      have hw1 : ‖w‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hw
      show ‖(r:ℂ) * w‖ < 1
      rw [norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpi : 0 < Real.pi := Real.pi_pos
    obtain ⟨s, b, hsb⟩ := htrig (fun w : ℂ => H ((r:ℂ) * w)) hgcont
      (Real.sqrt (ε / (4 * Real.pi))) (Real.sqrt_pos.mpr (by positivity))
    have hδsq : (Real.sqrt (ε / (4 * Real.pi)))^2 = ε / (4*Real.pi) :=
      Real.sq_sqrt (by positivity)
    have hunif : ∀ θ : ℝ,
        ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - ∑ j ∈ s, b j * ee j θ‖
          ≤ Real.sqrt (ε / (4 * Real.pi)) := by
      intro θ
      have hw1 : ‖Complex.exp ((θ:ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
      have h := hsb (Complex.exp ((θ:ℂ) * Complex.I)) hw1
      simpa only [hzpow] using h
    have hTcont : Continuous (fun θ : ℝ => ∑ j ∈ s, b j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    have hbound : (∫ θ in (0:ℝ)..(2*Real.pi),
        ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - ∑ j ∈ s, b j * ee j θ‖^2)
        ≤ (2*Real.pi) * (ε / (4*Real.pi)) := by
      have hint : IntervalIntegrable (fun θ : ℝ =>
          ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - ∑ j ∈ s, b j * ee j θ‖^2)
          volume 0 (2*Real.pi) :=
        (((hfcont.sub hTcont).norm).pow 2).intervalIntegrable _ _
      have hmono := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 2*Real.pi)
        (f := fun θ : ℝ =>
          ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - ∑ j ∈ s, b j * ee j θ‖^2)
        (g := fun _ : ℝ => ε / (4*Real.pi))
        (by positivity) hint intervalIntegrable_const
        (fun x _ => by
          have h1 := hunif x
          have h2 : (0:ℝ) ≤ ‖H ((r:ℂ) * Complex.exp ((x:ℂ) * Complex.I))
              - ∑ j ∈ s, b j * ee j x‖ := norm_nonneg _
          nlinarith [hδsq])
      rw [intervalIntegral.integral_const] at hmono
      simpa using hmono
    refine ⟨s.sup (fun j => j.natAbs) + n, fun N hN => ?_⟩
    have hsubwin : s ⊆ Finset.Icc (-(N:ℤ) - (n:ℤ)) ((N:ℤ) - (n:ℤ)) := by
      intro j hj
      have hjM : j.natAbs ≤ s.sup (fun j => j.natAbs) := Finset.le_sup hj
      have hNm : ((s.sup (fun j => j.natAbs) : ℕ) : ℤ) + (n:ℤ) ≤ (N:ℤ) := by exact_mod_cast hN
      simp only [Finset.mem_Icc]
      omega
    have hgoal : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), FourierCoefOfH n H k r
              * Complex.exp (((k - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
        = ∫ θ in (0:ℝ)..(2*Real.pi),
            ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
              - ∑ m ∈ Finset.Icc (-(N : ℤ) - (n:ℤ)) ((N : ℤ) - (n:ℤ)),
                  cf (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) m
                    * ee m θ‖ ^ 2 :=
      intervalIntegral.integral_congr (fun θ _ => by rw [hwin N θ])
    have hstep1 := hbest (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)))
      hfcont (Finset.Icc (-(N : ℤ) - (n:ℤ)) ((N : ℤ) - (n:ℤ)))
      (fun m => if m ∈ s then b m else 0)
    have hstep2 : (∫ θ in (0:ℝ)..(2*Real.pi),
        ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
          - ∑ m ∈ Finset.Icc (-(N : ℤ) - (n:ℤ)) ((N : ℤ) - (n:ℤ)),
              (if m ∈ s then b m else 0) * ee m θ‖^2)
        = ∫ θ in (0:ℝ)..(2*Real.pi),
            ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - ∑ j ∈ s, b j * ee j θ‖^2 :=
      intervalIntegral.integral_congr (fun θ _ => by rw [hextee s _ hsubwin b θ])
    have hnn : (0:ℝ) ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), FourierCoefOfH n H k r
              * Complex.exp (((k - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) (fun u _ => by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, hgoal]
    have hfin : (2*Real.pi) * (ε / (4*Real.pi)) < ε := by
      have h : (2*Real.pi) * (ε / (4*Real.pi)) = ε / 2 := by
        field_simp
        ring
      rw [h]
      linarith
    calc (∫ θ in (0:ℝ)..(2*Real.pi),
          ‖H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))
            - ∑ m ∈ Finset.Icc (-(N : ℤ) - (n:ℤ)) ((N : ℤ) - (n:ℤ)),
                cf (fun θ : ℝ => H ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))) m
                  * ee m θ‖ ^ 2)
        ≤ _ := hstep1
      _ = _ := hstep2
      _ ≤ (2*Real.pi) * (ε / (4*Real.pi)) := hbound
      _ < ε := hfin
  -- ## Assembling the six clauses
  refine ⟨hpartA, ?_, ?_, ?_, ?_, hpartF⟩
  · intro k c hcm d hdm
    exact ⟨(hcircAvg k).1 c hcm d hdm, (hcircAvg k).2.1 c hcm d hdm⟩
  · intro k
    exact (hcircAvg k).2.2.1
  · intro k
    exact (hcircAvg k).2.2.2.1
  · exact (hcircAvg 0).2.2.2.2
