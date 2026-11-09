import IwaniecManfredi.Preamble
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory

/-- Parseval's identity for the exponential system on `[0, 2π]`: for a
square-integrable `f` the sum over `m ∈ ℤ` of `2π |c_m|²`, with
`c_m = (1/2π) ∫₀^{2π} f(θ) e^{-imθ} dθ`, converges to `∫₀^{2π} |f|²`. -/
theorem ParsevalOnCircle (f : ℝ → ℂ) (hmeas : Measurable f)
    (hsq : IntegrableOn (fun θ : ℝ => ‖f θ‖ ^ 2) (Set.Ioc (0 : ℝ) (2 * Real.pi)) volume) :
    HasSum (fun m : ℤ => 2 * Real.pi *
        ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            f θ * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ‖ ^ 2) := by
  classical
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  -- ## the exponential family
  set ee : ℤ → ℝ → ℂ := fun m θ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) with heedef
  have heecont : ∀ m : ℤ, Continuous (ee m) := by intro m; rw [heedef]; fun_prop
  have heemul : ∀ (i m : ℤ) (θ : ℝ), ee i θ * ee m θ = ee (i + m) θ := by
    intro i m θ
    rw [heedef]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heeconj : ∀ (m : ℤ) (θ : ℝ), starRingEnd ℂ (ee m θ) = ee (-m) θ := by
    intro m θ
    rw [heedef]
    simp only [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have heeortho : ∀ m : ℤ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ee m θ) = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm; simp [heedef]
    · rw [if_neg hm]
      have hcne : ((m : ℂ) * Complex.I) ≠ 0 := by simp [hm]
      have h1 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (((m : ℂ) * Complex.I) * (θ : ℂ)))
          = (Complex.exp (((m : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ))
              - Complex.exp (((m : ℂ) * Complex.I) * ((0 : ℝ) : ℂ))) / ((m : ℂ) * Complex.I) :=
        integral_exp_mul_complex hcne
      have h2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), ee m θ)
          = ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (((m : ℂ) * Complex.I) * (θ : ℂ)) :=
        intervalIntegral.integral_congr (fun θ _ => by rw [heedef]; ring_nf)
      rw [h2, h1,
        show ((m : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I]
      simp
  -- ## conjugation
  have hconjon : ∀ (F : ℝ → ℂ) (s : Set ℝ), IntegrableOn F s volume →
      IntegrableOn (fun θ => starRingEnd ℂ (F θ)) s volume := by
    intro F s h
    refine MeasureTheory.Integrable.mono h ?_ (Filter.Eventually.of_forall (fun θ => by simp))
    exact Complex.continuous_conj.comp_aestronglyMeasurable h.1
  have hconjint : ∀ (F : ℝ → ℂ) (u v : ℝ), IntervalIntegrable F volume u v →
      IntervalIntegrable (fun θ => starRingEnd ℂ (F θ)) volume u v :=
    fun F u v h => ⟨hconjon F _ h.1, hconjon F _ h.2⟩
  have hivconj : ∀ (F : ℝ → ℂ) (u v : ℝ),
      (∫ θ in u..v, starRingEnd ℂ (F θ)) = starRingEnd ℂ (∫ θ in u..v, F θ) := by
    intro F u v
    simp only [intervalIntegral, map_sub]
    rw [← integral_conj, ← integral_conj]
  -- ## `f` is integrable on the period, and lies in `L²`
  have hfae : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    hmeas.aestronglyMeasurable
  have hfL1 : IntegrableOn f (Set.Ioc (0 : ℝ) (2 * Real.pi)) volume := by
    refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ => (1 + ‖f θ‖ ^ 2) / 2) ?_ hfae ?_
    · exact ((integrable_const (1 : ℝ)).add hsq).div_const 2
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      nlinarith [sq_nonneg (‖f θ‖ - 1), norm_nonneg (f θ)]
  have hf1 : IntervalIntegrable f volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi.le]
    exact hfL1
  -- casting a real interval-integrable function into `ℂ`
  have hofRealint : ∀ (g : ℝ → ℝ) (u v : ℝ), IntervalIntegrable g volume u v →
      IntervalIntegrable (fun θ => ((g θ : ℝ) : ℂ)) volume u v := by
    intro g u v h
    refine ⟨?_, ?_⟩
    · exact MeasureTheory.Integrable.mono h.1
        (Complex.continuous_ofReal.comp_aestronglyMeasurable h.1.1)
        (Filter.Eventually.of_forall (fun θ => by simp))
    · exact MeasureTheory.Integrable.mono h.2
        (Complex.continuous_ofReal.comp_aestronglyMeasurable h.2.1)
        (Filter.Eventually.of_forall (fun θ => by simp))
  have hsq' : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
    intro z
    rw [Complex.ofReal_pow]
    exact (RCLike.mul_conj z).symm
  -- ## the coefficients
  set cc : ℤ → ℂ := fun m =>
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * ee (-m) θ with hccdef
  have hccgoal : ∀ m : ℤ, (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      f θ * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I) = cc m := by
    intro m
    rw [hccdef]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [heedef]
    push_cast
    ring_nf
  have hcfi : ∀ m : ℤ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * ee (-m) θ) = (2 * Real.pi : ℂ) * cc m := by
    intro m
    rw [hccdef]
    have hpine : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  -- ## the single-mode integral of a trigonometric sum
  have hsumee : ∀ (s : Finset ℤ) (b : ℤ → ℂ) (i : ℤ), i ∈ s →
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ j ∈ s, b j * ee (j + -i) θ)
        = (2 * Real.pi : ℂ) * b i := by
    intro s b i hi
    have hterms : ∀ j ∈ s, IntervalIntegrable (fun θ => b j * ee (j + -i) θ)
        volume 0 (2 * Real.pi) :=
      fun j _ => (continuous_const.mul (heecont (j + -i))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hterms]
    have hstep : ∀ j ∈ s, (∫ θ in (0 : ℝ)..(2 * Real.pi), b j * ee (j + -i) θ)
        = (if j = i then (2 * Real.pi : ℂ) * b j else 0) := by
      intro j _
      rw [intervalIntegral.integral_const_mul, heeortho]
      by_cases h : j = i
      · simp [h, mul_comm]
      · have hne : j + -i ≠ 0 := by omega
        simp [hne, h]
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' s i (fun j => (2 * Real.pi : ℂ) * b j),
      if_pos hi]
  have hDee : ∀ (s : Finset ℤ) (b : ℤ → ℂ) (i : ℤ), i ∈ s →
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (∑ j ∈ s, b j * ee j θ) * ee (-i) θ)
        = (2 * Real.pi : ℂ) * b i := by
    intro s b i hi
    rw [← hsumee s b i hi]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc, heemul])
  -- ## the Fourier coefficients of a residual
  have hresid : ∀ (s : Finset ℤ) (b : ℤ → ℂ) (i : ℤ), i ∈ s →
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ - ∑ j ∈ s, b j * ee j θ) * ee (-i) θ)
        = (2 * Real.pi : ℂ) * (cc i - b i) := by
    intro s b i hi
    have hint1 : IntervalIntegrable (fun θ => f θ * ee (-i) θ) volume 0 (2 * Real.pi) :=
      hf1.mul_continuousOn ((heecont (-i)).continuousOn)
    have hint2 : IntervalIntegrable (fun θ => (∑ j ∈ s, b j * ee j θ) * ee (-i) θ)
        volume 0 (2 * Real.pi) :=
      ((continuous_finsetSum s
        (fun j _ => continuous_const.mul (heecont j))).intervalIntegrable _ _).mul_continuousOn
          ((heecont (-i)).continuousOn)
    have hpt : ∀ θ : ℝ, (f θ - ∑ j ∈ s, b j * ee j θ) * ee (-i) θ
        = f θ * ee (-i) θ - (∑ j ∈ s, b j * ee j θ) * ee (-i) θ := fun θ => by ring
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
      intervalIntegral.integral_sub hint1 hint2, hcfi i, hDee s b i hi]
    ring
  -- ## Pythagoras
  have hpythag : ∀ (R : ℝ → ℂ), IntervalIntegrable R volume 0 (2 * Real.pi) →
      IntervalIntegrable (fun θ => ‖R θ‖ ^ 2) volume 0 (2 * Real.pi) →
      ∀ (s : Finset ℤ) (c : ℤ → ℂ),
      (∀ j ∈ s, (∫ θ in (0 : ℝ)..(2 * Real.pi), R θ * ee (-j) θ) = 0) →
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖R θ + ∑ j ∈ s, c j * ee j θ‖ ^ 2)
        = (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖R θ‖ ^ 2)
          + ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖∑ j ∈ s, c j * ee j θ‖ ^ 2 := by
    intro R hR1 hR2 s c h0
    have hDcont : Continuous (fun θ : ℝ => ∑ j ∈ s, c j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    set D : ℝ → ℂ := fun θ => ∑ j ∈ s, c j * ee j θ with hDdef
    have hcross1 : (∫ θ in (0 : ℝ)..(2 * Real.pi), R θ * starRingEnd ℂ (D θ)) = 0 := by
      have hpt : ∀ θ : ℝ, R θ * starRingEnd ℂ (D θ)
          = ∑ j ∈ s, starRingEnd ℂ (c j) * (R θ * ee (-j) θ) := by
        intro θ
        rw [hDdef]
        simp only [map_sum, map_mul, heeconj]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hterms : ∀ j ∈ s, IntervalIntegrable
          (fun θ => starRingEnd ℂ (c j) * (R θ * ee (-j) θ)) volume 0 (2 * Real.pi) :=
        fun j _ => (hR1.mul_continuousOn ((heecont (-j)).continuousOn)).const_mul _
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_finsetSum hterms]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [intervalIntegral.integral_const_mul, h0 j hj, mul_zero]
    have hcross2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), D θ * starRingEnd ℂ (R θ)) = 0 := by
      have h := hivconj (fun θ => R θ * starRingEnd ℂ (D θ)) 0 (2 * Real.pi)
      rw [hcross1, map_zero] at h
      rw [← h]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [map_mul, Complex.conj_conj]
      ring
    have hintRR : IntervalIntegrable (fun θ => R θ * starRingEnd ℂ (R θ))
        volume 0 (2 * Real.pi) := by
      refine (hofRealint (fun θ => ‖R θ‖ ^ 2) 0 (2 * Real.pi) hR2).congr ?_
      exact fun θ _ => hsq' (R θ)
    have hintDD : IntervalIntegrable (fun θ => D θ * starRingEnd ℂ (D θ))
        volume 0 (2 * Real.pi) :=
      (hDcont.mul (Complex.continuous_conj.comp hDcont)).intervalIntegrable _ _
    have hintRD : IntervalIntegrable (fun θ => R θ * starRingEnd ℂ (D θ))
        volume 0 (2 * Real.pi) :=
      hR1.mul_continuousOn ((Complex.continuous_conj.comp hDcont).continuousOn)
    have hintDR : IntervalIntegrable (fun θ => D θ * starRingEnd ℂ (R θ))
        volume 0 (2 * Real.pi) :=
      (hconjint R 0 (2 * Real.pi) hR1).continuousOn_mul hDcont.continuousOn
    have hmain : ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖R θ + D θ‖ ^ 2 : ℝ) : ℂ)
        = ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖R θ‖ ^ 2 : ℝ) : ℂ)
          + ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖D θ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
        ← intervalIntegral.integral_ofReal]
      have hpt : ∀ θ : ℝ, ((‖R θ + D θ‖ ^ 2 : ℝ) : ℂ)
          = ((R θ * starRingEnd ℂ (R θ)) + (D θ * starRingEnd ℂ (D θ)))
            + ((R θ * starRingEnd ℂ (D θ)) + (D θ * starRingEnd ℂ (R θ))) := by
        intro θ
        rw [hsq', map_add]
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_add (hintRR.add hintDD) (hintRD.add hintDR),
        intervalIntegral.integral_add hintRR hintDD,
        intervalIntegral.integral_add hintRD hintDR, hcross1, hcross2,
        intervalIntegral.integral_congr
          (fun θ (_ : θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi)) => hsq' (R θ)),
        intervalIntegral.integral_congr
          (fun θ (_ : θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi)) => hsq' (D θ))]
      ring
    exact_mod_cast hmain
  -- ## the squared norm of a Fourier partial sum
  have hDnorm : ∀ s : Finset ℤ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖∑ j ∈ s, cc j * ee j θ‖ ^ 2)
        = 2 * Real.pi * ∑ j ∈ s, ‖cc j‖ ^ 2 := by
    intro s
    have hDcont : Continuous (fun θ : ℝ => ∑ j ∈ s, cc j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    have hmain : ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖∑ j ∈ s, cc j * ee j θ‖ ^ 2 : ℝ) : ℂ)
        = ((2 * Real.pi * ∑ j ∈ s, ‖cc j‖ ^ 2 : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      have hpt : ∀ θ : ℝ, ((‖∑ j ∈ s, cc j * ee j θ‖ ^ 2 : ℝ) : ℂ)
          = ∑ j ∈ s, starRingEnd ℂ (cc j) * ((∑ i ∈ s, cc i * ee i θ) * ee (-j) θ) := by
        intro θ
        rw [hsq']
        simp only [map_sum, map_mul, heeconj]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hterms : ∀ j ∈ s, IntervalIntegrable
          (fun θ => starRingEnd ℂ (cc j) * ((∑ i ∈ s, cc i * ee i θ) * ee (-j) θ))
          volume 0 (2 * Real.pi) :=
        fun j _ => ((hDcont.intervalIntegrable _ _).mul_continuousOn
          ((heecont (-j)).continuousOn)).const_mul _
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_finsetSum hterms]
      have hstep : ∀ j ∈ s,
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            starRingEnd ℂ (cc j) * ((∑ i ∈ s, cc i * ee i θ) * ee (-j) θ))
            = ((2 * Real.pi : ℝ) : ℂ) * ((‖cc j‖ ^ 2 : ℝ) : ℂ) := by
        intro j hj
        rw [intervalIntegral.integral_const_mul, hDee s cc j hj, hsq' (cc j)]
        push_cast
        ring
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
      push_cast
      ring
    exact_mod_cast hmain
  -- ## Bessel's identity
  have hbessel : ∀ s : Finset ℤ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ‖ ^ 2)
        = (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - ∑ j ∈ s, cc j * ee j θ‖ ^ 2)
          + 2 * Real.pi * ∑ j ∈ s, ‖cc j‖ ^ 2 := by
    intro s
    have hDcont : Continuous (fun θ : ℝ => ∑ j ∈ s, cc j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    have hR1 : IntervalIntegrable (fun θ : ℝ => f θ - ∑ j ∈ s, cc j * ee j θ)
        volume 0 (2 * Real.pi) := hf1.sub (hDcont.intervalIntegrable _ _)
    have hR2 : IntervalIntegrable (fun θ : ℝ => ‖f θ - ∑ j ∈ s, cc j * ee j θ‖ ^ 2)
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi.le]
      refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ =>
        2 * ‖f θ‖ ^ 2 + 2 * ‖(∑ j ∈ s, cc j * ee j θ)‖ ^ 2) ?_ ?_ ?_
      · exact (hsq.const_mul 2).add
          ((((hDcont.norm.pow 2).intervalIntegrable 0 (2 * Real.pi)).1).const_mul 2)
      · exact (((hmeas.sub hDcont.measurable).norm).pow_const 2).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun θ => ?_)
        have h1 := norm_sub_le (f θ) (∑ j ∈ s, cc j * ee j θ)
        have h2 : (0 : ℝ) ≤ ‖f θ‖ := norm_nonneg _
        have h3 : (0 : ℝ) ≤ ‖(∑ j ∈ s, cc j * ee j θ)‖ := norm_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (‖f θ‖ - ‖(∑ j ∈ s, cc j * ee j θ)‖),
          norm_nonneg (f θ - ∑ j ∈ s, cc j * ee j θ)]
    have h0 : ∀ j ∈ s, (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (f θ - ∑ i ∈ s, cc i * ee i θ) * ee (-j) θ) = 0 := by
      intro j hj
      rw [hresid s cc j hj, sub_self, mul_zero]
    rw [show (fun θ : ℝ => ‖f θ‖ ^ 2)
        = (fun θ : ℝ => ‖(f θ - ∑ j ∈ s, cc j * ee j θ) + ∑ j ∈ s, cc j * ee j θ‖ ^ 2) from by
          funext θ; rw [sub_add_cancel],
      hpythag _ hR1 hR2 s cc h0, hDnorm s]
  -- ## the partial sum is the best approximation from its own window
  have hbest : ∀ (s : Finset ℤ) (b : ℤ → ℂ),
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - ∑ j ∈ s, cc j * ee j θ‖ ^ 2)
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - ∑ j ∈ s, b j * ee j θ‖ ^ 2 := by
    intro s b
    have hDcont : Continuous (fun θ : ℝ => ∑ j ∈ s, cc j * ee j θ) :=
      continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
    have hR1 : IntervalIntegrable (fun θ : ℝ => f θ - ∑ j ∈ s, cc j * ee j θ)
        volume 0 (2 * Real.pi) := hf1.sub (hDcont.intervalIntegrable _ _)
    have hR2 : IntervalIntegrable (fun θ : ℝ => ‖f θ - ∑ j ∈ s, cc j * ee j θ‖ ^ 2)
        volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi.le]
      refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ =>
        2 * ‖f θ‖ ^ 2 + 2 * ‖(∑ j ∈ s, cc j * ee j θ)‖ ^ 2) ?_ ?_ ?_
      · exact (hsq.const_mul 2).add
          ((((hDcont.norm.pow 2).intervalIntegrable 0 (2 * Real.pi)).1).const_mul 2)
      · exact (((hmeas.sub hDcont.measurable).norm).pow_const 2).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun θ => ?_)
        have h1 := norm_sub_le (f θ) (∑ j ∈ s, cc j * ee j θ)
        have h2 : (0 : ℝ) ≤ ‖f θ‖ := norm_nonneg _
        have h3 : (0 : ℝ) ≤ ‖(∑ j ∈ s, cc j * ee j θ)‖ := norm_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (‖f θ‖ - ‖(∑ j ∈ s, cc j * ee j θ)‖),
          norm_nonneg (f θ - ∑ j ∈ s, cc j * ee j θ)]
    have h0 : ∀ j ∈ s, (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (f θ - ∑ i ∈ s, cc i * ee i θ) * ee (-j) θ) = 0 := by
      intro j hj
      rw [hresid s cc j hj, sub_self, mul_zero]
    have hsplit : (fun θ : ℝ => ‖f θ - ∑ j ∈ s, b j * ee j θ‖ ^ 2)
        = (fun θ : ℝ => ‖(f θ - ∑ j ∈ s, cc j * ee j θ)
            + ∑ j ∈ s, (cc j - b j) * ee j θ‖ ^ 2) := by
      funext θ
      have hs : ∑ j ∈ s, (cc j - b j) * ee j θ
          = (∑ j ∈ s, cc j * ee j θ) - ∑ j ∈ s, b j * ee j θ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hs, show (f θ - ∑ j ∈ s, cc j * ee j θ)
            + ((∑ j ∈ s, cc j * ee j θ) - ∑ j ∈ s, b j * ee j θ)
          = f θ - ∑ j ∈ s, b j * ee j θ from by ring]
    rw [hsplit, hpythag _ hR1 hR2 s (fun j => cc j - b j) h0]
    have hnn : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖∑ j ∈ s, (cc j - b j) * ee j θ‖ ^ 2 :=
      intervalIntegral.integral_nonneg h2pi.le (fun u _ => by positivity)
    linarith
  -- ## uniform approximation on the unit circle by Laurent polynomials (Stone--Weierstrass)
  have htrig : ∀ (g : ℂ → ℂ), ContinuousOn g (Metric.sphere (0 : ℂ) 1) → ∀ ε : ℝ, 0 < ε →
      ∃ (s : Finset ℤ) (b : ℤ → ℂ), ∀ w : ℂ, ‖w‖ = 1 →
        ‖g w - ∑ j ∈ s, b j * w ^ j‖ ≤ ε := by
    intro g hg ε hε
    have hnorm1 : ∀ w : ↥(Metric.sphere (0 : ℂ) 1), ‖(w : ℂ)‖ = 1 := by
      intro w
      have hw := w.2
      simp
    have hne : ∀ w : ↥(Metric.sphere (0 : ℂ) 1), ((w : ℂ)) ≠ 0 := by
      intro w h
      have hw := hnorm1 w
      rw [h] at hw; simp at hw
    set mono : ℤ → C(↥(Metric.sphere (0 : ℂ) 1), ℂ) := fun m => ⟨fun w => (w : ℂ) ^ m, by
      exact Continuous.zpow₀ continuous_subtype_val m (fun w => Or.inl (hne w))⟩ with hmonodef
    have hmono_apply : ∀ (m : ℤ) (w : ↥(Metric.sphere (0 : ℂ) 1)), mono m w = (w : ℂ) ^ m :=
      fun _ _ => rfl
    have hmono_zero : mono 0 = 1 := by ext w; simp [hmono_apply]
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
    set A : StarSubalgebra ℂ C(↥(Metric.sphere (0 : ℂ) 1), ℂ) :=
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
    have hApoly : ∀ x : C(↥(Metric.sphere (0 : ℂ) 1), ℂ), x ∈ A →
        ∃ (s : Finset ℤ) (b : ℤ → ℂ), ∀ w : ↥(Metric.sphere (0 : ℂ) 1),
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
    have hGmem : (⟨Set.domRestrict (Metric.sphere (0 : ℂ) 1) g, hg.domRestrict⟩ :
        C(↥(Metric.sphere (0 : ℂ) 1), ℂ))
          ∈ closure (A : Set C(↥(Metric.sphere (0 : ℂ) 1), ℂ)) := by
      have h : (⟨Set.domRestrict (Metric.sphere (0 : ℂ) 1) g, hg.domRestrict⟩ :
          C(↥(Metric.sphere (0 : ℂ) 1), ℂ)) ∈ A.topologicalClosure := by
        rw [hAtop]; exact StarSubalgebra.mem_top
      exact h
    obtain ⟨P, hPA, hPdist⟩ := Metric.mem_closure_iff.mp hGmem ε hε
    obtain ⟨s, b, hsb⟩ := hApoly P hPA
    refine ⟨s, b, ?_⟩
    intro w hw
    have hwZ : w ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hle := ContinuousMap.dist_apply_le_dist
      (f := (⟨Set.domRestrict (Metric.sphere (0 : ℂ) 1) g, hg.domRestrict⟩ :
        C(↥(Metric.sphere (0 : ℂ) 1), ℂ))) (g := P) (⟨w, hwZ⟩ : ↥(Metric.sphere (0 : ℂ) 1))
    rw [dist_eq_norm] at hle
    have hPval : P (⟨w, hwZ⟩ : ↥(Metric.sphere (0 : ℂ) 1)) = ∑ j ∈ s, b j * w ^ j := hsb _
    rw [hPval] at hle
    exact le_trans hle hPdist.le
  -- ## a continuous function vanishing near the ends of a period lifts to the unit circle
  have hsphere : ∀ w : ℂ, ‖w‖ = 1 → w.im = 0 → w = 1 ∨ w = -1 := by
    intro w hw him
    have h2 : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [Complex.normSq_apply, him] at h2
    have h1 : w.re ^ 2 = 1 := by nlinarith
    have h3 : w.re = 1 ∨ w.re = -1 := by
      have : (w.re - 1) * (w.re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases h3 with h | h
    · left
      apply Complex.ext <;> simp [h, him]
    · right
      apply Complex.ext <;> simp [h, him]
  have hlift : ∀ (u : ℝ → ℂ) (ρ : ℝ), Continuous u → 0 < ρ → ρ < Real.pi →
      (∀ θ : ℝ, θ ∉ Set.Ioo ρ (2 * Real.pi - ρ) → u θ = 0) →
      ∃ G : ℂ → ℂ, ContinuousOn G (Metric.sphere (0 : ℂ) 1) ∧
        ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          G (Complex.exp ((θ : ℂ) * Complex.I)) = u θ := by
    intro u ρ hu hρ0 hρπ huvan
    have hcosρ : Real.cos ρ < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hρπ.le hρ0
      rwa [Real.cos_zero] at h
    have hvannbhd : ∀ w : ℂ, ‖w‖ = 1 → Real.cos ρ < w.re →
        u (Complex.arg (-w) + Real.pi) = 0 := by
      intro w hw hre
      refine huvan _ ?_
      have hwne : (-w) ≠ 0 := by
        simp only [ne_eq, neg_eq_zero]
        intro h
        rw [h] at hw
        simp at hw
      have hcosarg : Real.cos (Complex.arg (-w)) = -w.re := by
        rw [Complex.cos_arg hwne]
        simp [hw]
      have habs : Real.pi - ρ < |Complex.arg (-w)| := by
        rcases lt_or_ge (Real.pi - ρ) |Complex.arg (-w)| with h | h
        · exact h
        · exfalso
          have h1 : Real.cos (Real.pi - ρ) ≤ Real.cos |Complex.arg (-w)| :=
            Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h
          rw [Real.cos_abs, hcosarg, Real.cos_pi_sub] at h1
          linarith
      intro hmem
      obtain ⟨h1, h2⟩ := hmem
      have hlt : |Complex.arg (-w)| < Real.pi - ρ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    refine ⟨fun w => u (Complex.arg (-w) + Real.pi), ?_, ?_⟩
    · intro w hw
      have hw1 : ‖w‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hw
      by_cases hwe : w = 1
      · -- `G` vanishes on a neighbourhood of `1` inside the sphere
        have hnb : {z : ℂ | Real.cos ρ < z.re} ∈ nhds w := by
          refine IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) ?_
          rw [hwe]
          simpa using hcosρ
        have hzero : ∀ᶠ z in nhdsWithin w (Metric.sphere (0 : ℂ) 1),
            u (Complex.arg (-z) + Real.pi) = 0 := by
          filter_upwards [nhdsWithin_le_nhds hnb, self_mem_nhdsWithin] with z hz1 hz2
          exact hvannbhd z (by simpa [Metric.mem_sphere, dist_zero_right] using hz2) hz1
        have hGw : u (Complex.arg (-w) + Real.pi) = 0 := hvannbhd w hw1 (by rw [hwe]; simpa using hcosρ)
        rw [ContinuousWithinAt, hGw]
        exact (Filter.tendsto_congr' hzero).mpr tendsto_const_nhds
      · have hslit : (-w) ∈ Complex.slitPlane := by
          rcases eq_or_ne w.im 0 with him | him
          · rcases hsphere w hw1 him with h | h
            · exact absurd h hwe
            · left
              rw [h]
              norm_num
          · right
            simpa using him
        have hcont : ContinuousAt (fun z : ℂ => u (Complex.arg (-z) + Real.pi)) w := by
          refine hu.continuousAt.comp ?_
          exact ((Complex.continuousAt_arg hslit).comp (continuous_neg.continuousAt)).add
            continuousAt_const
        exact hcont.continuousWithinAt
    · intro θ hθ
      obtain ⟨hθ0, hθ2⟩ := hθ
      show u (Complex.arg (-(Complex.exp ((θ : ℂ) * Complex.I))) + Real.pi) = u θ
      rcases eq_or_lt_of_le hθ0 with h0 | h0
      · -- `θ = 0`
        rw [← h0]
        rw [show Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 from by norm_num,
          Complex.arg_neg_one]
        rw [huvan (Real.pi + Real.pi) (by
          intro hmem
          have := hmem.2
          linarith), huvan 0 (by
          intro hmem
          have := hmem.1
          linarith)]
      rcases eq_or_lt_of_le hθ2 with h2 | h2
      · -- `θ = 2π`
        rw [h2, show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 from by
          rw [show (((2 * Real.pi : ℝ) : ℂ)) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from by
            push_cast; ring]
          exact Complex.exp_two_pi_mul_I, Complex.arg_neg_one]
        rw [huvan (Real.pi + Real.pi) (by
          intro hmem
          have := hmem.2
          linarith), huvan (2 * Real.pi) (by
          intro hmem
          have := hmem.2
          linarith)]
      · -- `0 < θ < 2π`
        have hneg : -Complex.exp ((θ : ℂ) * Complex.I)
            = Complex.exp (((θ - Real.pi : ℝ) : ℂ) * Complex.I) := by
          rw [show (((θ - Real.pi : ℝ) : ℂ)) * Complex.I
              = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I * (-1) from by push_cast; ring,
            Complex.exp_add]
          rw [show (Real.pi : ℂ) * Complex.I * (-1) = -((Real.pi : ℂ) * Complex.I) from by ring,
            Complex.exp_neg, Complex.exp_pi_mul_I]
          simp
        rw [hneg, Complex.exp_mul_I,
          Complex.arg_cos_add_sin_mul_I (θ := θ - Real.pi) ⟨by linarith, by linarith⟩]
        congr 1
        ring
  -- ## a Urysohn cutoff for the period
  have hcut : ∀ δ : ℝ, 0 < δ → δ < Real.pi → ∃ χ : ℝ → ℝ, Continuous χ ∧
      (∀ θ, χ θ ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ θ ∈ Set.Icc δ (2 * Real.pi - δ), χ θ = 1) ∧
      (∀ θ, θ ∉ Set.Ioo (δ / 2) (2 * Real.pi - δ / 2) → χ θ = 0) := by
    intro δ hδ hδπ
    have hdisj : Disjoint ((Set.Ioo (δ / 2) (2 * Real.pi - δ / 2))ᶜ)
        (Set.Icc δ (2 * Real.pi - δ)) := by
      rw [Set.disjoint_compl_left_iff_subset]
      intro θ hθ
      exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    obtain ⟨χ, h0, h1, hIcc⟩ := exists_continuous_zero_one_of_isClosed
      (isOpen_Ioo.isClosed_compl) isClosed_Icc hdisj
    exact ⟨χ, χ.continuous, hIcc, fun θ hθ => h1 hθ, fun θ hθ => h0 hθ⟩
  -- ## `f` as an `L²` function on the line
  have hFmeas : Measurable (Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f) :=
    hmeas.indicator measurableSet_Ioc
  have hFsqeq : (fun θ : ℝ => ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f θ‖ ^ 2)
      = Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) (fun θ => ‖f θ‖ ^ 2) := by
    funext θ
    by_cases hθ : θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ]; simp
  have hFsq : Integrable
      (fun θ : ℝ => ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f θ‖ ^ 2) volume := by
    rw [hFsqeq]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).mpr hsq
  have hFLp : MemLp (Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f)
      (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ENNReal) from by norm_num,
      ← MeasureTheory.integrable_norm_rpow_iff hFmeas.aestronglyMeasurable
      (by norm_num) (by norm_num)]
    simpa using hFsq
  -- ## trigonometric polynomials approximate `f` in `L²(0, 2π)`
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℤ) (b : ℤ → ℂ),
      (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - ∑ j ∈ s, b j * ee j θ‖ ^ 2) ≤ ε := by
    intro ε hε
    obtain ⟨hh, hhcs, hhle, hhcont, hhLp⟩ :=
      hFLp.exists_hasCompactSupport_integral_rpow_sub_le (p := 2) (by norm_num)
        (ε := ε / 9) (by positivity)
    obtain ⟨Cb, hCb⟩ := HasCompactSupport.exists_bound_of_continuous hhcs hhcont
    have hCb0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb 0)
    -- the cutoff width
    have hδ0 : 0 < min (Real.pi / 2) (ε / (18 * (Cb ^ 2 + 1))) := by positivity
    have hδπ : min (Real.pi / 2) (ε / (18 * (Cb ^ 2 + 1))) < Real.pi :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨χ, hχcont, hχIcc, hχone, hχzero⟩ :=
      hcut (min (Real.pi / 2) (ε / (18 * (Cb ^ 2 + 1)))) hδ0 hδπ
    set δ : ℝ := min (Real.pi / 2) (ε / (18 * (Cb ^ 2 + 1))) with hδdef
    have hδbound : Cb ^ 2 * (2 * δ) ≤ ε / 9 := by
      have h1 : δ ≤ ε / (18 * (Cb ^ 2 + 1)) := min_le_right _ _
      have hpos : (0 : ℝ) < 18 * (Cb ^ 2 + 1) := by positivity
      have h2 : δ * (18 * (Cb ^ 2 + 1))
          ≤ (ε / (18 * (Cb ^ 2 + 1))) * (18 * (Cb ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
      nlinarith [hδ0.le, sq_nonneg Cb]
    -- the cut-off continuous approximation and its lift
    have hucont : Continuous (fun θ : ℝ => ((χ θ : ℝ) : ℂ) * hh θ) := by
      exact (Complex.continuous_ofReal.comp hχcont).mul hhcont
    have huvan : ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (2 * Real.pi - δ / 2) →
        ((χ θ : ℝ) : ℂ) * hh θ = 0 := by
      intro θ hθ
      rw [hχzero θ hθ]
      simp
    obtain ⟨G, hGcont, hGval⟩ := hlift (fun θ : ℝ => ((χ θ : ℝ) : ℂ) * hh θ) (δ / 2) hucont
      (by positivity) (by linarith) huvan
    set η : ℝ := Real.sqrt (ε / (9 * (2 * Real.pi))) with hηdef
    have hη0 : 0 < η := Real.sqrt_pos.mpr (by positivity)
    have hηsq : η ^ 2 = ε / (9 * (2 * Real.pi)) := Real.sq_sqrt (by positivity)
    obtain ⟨s, b, hsb⟩ := htrig G hGcont η hη0
    refine ⟨s, b, ?_⟩
    -- the uniform bound transported to the interval
    have hTbound : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖((χ θ : ℝ) : ℂ) * hh θ - ∑ j ∈ s, b j * ee j θ‖ ≤ η := by
      intro θ hθ
      have hw : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
      have h := hsb (Complex.exp ((θ : ℂ) * Complex.I)) hw
      rw [hGval θ hθ] at h
      refine le_trans (le_of_eq ?_) h
      congr 2
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      show Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) ^ j
      rw [← Complex.exp_int_mul]
      congr 1
      ring
    -- the pointwise bound on the period
    have hptb : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖f θ - ∑ j ∈ s, b j * ee j θ‖ ^ 2
          ≤ 3 * (‖f θ - hh θ‖ ^ 2 + Cb ^ 2 * (1 - χ θ) + η ^ 2) := by
      intro θ hθ
      obtain ⟨hχ0, hχ1⟩ := hχIcc θ
      have hb1 : ‖(((1 - χ θ : ℝ)) : ℂ) * hh θ‖ ≤ (1 - χ θ) * Cb := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_left (hCb θ) (by linarith)
      have hsplit : f θ - ∑ j ∈ s, b j * ee j θ
          = (f θ - hh θ) + ((((1 - χ θ : ℝ)) : ℂ) * hh θ)
            + ((((χ θ : ℝ)) : ℂ) * hh θ - ∑ j ∈ s, b j * ee j θ) := by push_cast; ring
      have htri : ‖f θ - ∑ j ∈ s, b j * ee j θ‖
          ≤ ‖f θ - hh θ‖ + (1 - χ θ) * Cb + η := by
        rw [hsplit]
        have t1 := norm_add_le ((f θ - hh θ) + ((((1 - χ θ : ℝ)) : ℂ) * hh θ))
          ((((χ θ : ℝ)) : ℂ) * hh θ - ∑ j ∈ s, b j * ee j θ)
        have t2 := norm_add_le (f θ - hh θ) ((((1 - χ θ : ℝ)) : ℂ) * hh θ)
        have t3 := hTbound θ hθ
        linarith
      have hsq1 : (1 - χ θ) ^ 2 ≤ 1 - χ θ := by nlinarith
      have h1 : (0 : ℝ) ≤ ‖f θ - hh θ‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ (1 - χ θ) * Cb := by positivity
      nlinarith [norm_nonneg (f θ - ∑ j ∈ s, b j * ee j θ), sq_nonneg (‖f θ - hh θ‖ - η),
        sq_nonneg (‖f θ - hh θ‖ - (1 - χ θ) * Cb), sq_nonneg ((1 - χ θ) * Cb - η),
        mul_le_mul_of_nonneg_right hsq1 (sq_nonneg Cb)]
    -- integrability of the three pieces
    have hhcontint : IntervalIntegrable (fun θ : ℝ => ‖hh θ‖ ^ 2) volume 0 (2 * Real.pi) :=
      ((hhcont.norm).pow 2).intervalIntegrable _ _
    have hAint : IntervalIntegrable (fun θ : ℝ => ‖f θ - hh θ‖ ^ 2) volume 0 (2 * Real.pi) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi.le]
      refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ =>
        2 * ‖f θ‖ ^ 2 + 2 * ‖hh θ‖ ^ 2) ?_ ?_ ?_
      · exact (hsq.const_mul 2).add (hhcontint.1.const_mul 2)
      · exact (((hmeas.sub hhcont.measurable).norm).pow_const 2).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun θ => ?_)
        have h1 := norm_sub_le (f θ) (hh θ)
        have h2 : (0 : ℝ) ≤ ‖f θ‖ := norm_nonneg _
        have h3 : (0 : ℝ) ≤ ‖hh θ‖ := norm_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (‖f θ‖ - ‖hh θ‖), norm_nonneg (f θ - hh θ)]
    have hBint : IntervalIntegrable (fun θ : ℝ => Cb ^ 2 * (1 - χ θ)) volume 0 (2 * Real.pi) :=
      ((continuous_const.mul (continuous_const.sub hχcont))).intervalIntegrable _ _
    have hCint : IntervalIntegrable (fun _ : ℝ => η ^ 2) volume 0 (2 * Real.pi) :=
      intervalIntegrable_const
    have hfTint : IntervalIntegrable (fun θ : ℝ => ‖f θ - ∑ j ∈ s, b j * ee j θ‖ ^ 2)
        volume 0 (2 * Real.pi) := by
      have hDcont : Continuous (fun θ : ℝ => ∑ j ∈ s, b j * ee j θ) :=
        continuous_finsetSum s (fun j _ => continuous_const.mul (heecont j))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi.le]
      refine MeasureTheory.Integrable.mono' (g := fun θ : ℝ =>
        2 * ‖f θ‖ ^ 2 + 2 * ‖(∑ j ∈ s, b j * ee j θ)‖ ^ 2) ?_ ?_ ?_
      · exact (hsq.const_mul 2).add
          ((((hDcont.norm.pow 2).intervalIntegrable 0 (2 * Real.pi)).1).const_mul 2)
      · exact (((hmeas.sub hDcont.measurable).norm).pow_const 2).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun θ => ?_)
        have h1 := norm_sub_le (f θ) (∑ j ∈ s, b j * ee j θ)
        have h2 : (0 : ℝ) ≤ ‖f θ‖ := norm_nonneg _
        have h3 : (0 : ℝ) ≤ ‖(∑ j ∈ s, b j * ee j θ)‖ := norm_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (‖f θ‖ - ‖(∑ j ∈ s, b j * ee j θ)‖),
          norm_nonneg (f θ - ∑ j ∈ s, b j * ee j θ)]
    -- (A) the `L²` error of the continuous approximation
    have hFhLp : MemLp (Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f - hh) 2 volume := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num]
      exact hFLp.sub hhLp
    have hFhint : Integrable (fun x : ℝ =>
        ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f x - hh x‖ ^ 2) volume := by
      have h := (MeasureTheory.integrable_norm_rpow_iff
        (f := Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f - hh) (p := 2) hFhLp.1
        (by norm_num) (by norm_num)).mpr hFhLp
      simpa using h
    have hA : (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - hh θ‖ ^ 2) ≤ ε / 9 := by
      have hconv : ∀ x : ℝ,
          ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f x - hh x‖ ^ (2 : ℝ)
            = ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f x - hh x‖ ^ (2 : ℕ) := by
        intro x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hconv)] at hhle
      rw [intervalIntegral.integral_of_le h2pi.le,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (fun θ hθ => by
            show ‖f θ - hh θ‖ ^ 2
              = ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f θ - hh θ‖ ^ 2
            rw [Set.indicator_of_mem hθ] :
            Set.EqOn (fun θ => ‖f θ - hh θ‖ ^ 2)
              (fun θ => ‖Set.indicator (Set.Ioc (0 : ℝ) (2 * Real.pi)) f θ - hh θ‖ ^ 2)
              (Set.Ioc (0 : ℝ) (2 * Real.pi)))]
      refine le_trans (MeasureTheory.setIntegral_le_integral hFhint
        (Filter.Eventually.of_forall (fun x => by positivity))) ?_
      exact hhle
    -- (B) the cutoff loses little
    have hB : (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 - χ θ)) ≤ 2 * δ := by
      have hc : Continuous (fun θ : ℝ => 1 - χ θ) := continuous_const.sub hχcont
      have hδle : δ ≤ 2 * Real.pi - δ := by
        have h1 : δ ≤ Real.pi / 2 := min_le_left _ _
        linarith [Real.pi_pos]
      have h1 : (∫ θ in (0 : ℝ)..δ, (1 - χ θ)) ≤ δ := by
        have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := δ) hδ0.le
          (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
          (fun x _ => by linarith [(hχIcc x).1])
        rw [intervalIntegral.integral_const] at h
        simpa using h
      have h2 : (∫ θ in δ..(2 * Real.pi - δ), (1 - χ θ)) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_]
        · simp
        · intro x hx
          rw [Set.uIcc_of_le hδle] at hx
          simp [hχone x hx]
      have h3 : (∫ θ in (2 * Real.pi - δ)..(2 * Real.pi), (1 - χ θ)) ≤ δ := by
        have h := intervalIntegral.integral_mono_on (a := 2 * Real.pi - δ) (b := 2 * Real.pi)
          (by linarith) (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
          (fun x _ => by linarith [(hχIcc x).1])
        rw [intervalIntegral.integral_const] at h
        simpa using h
      have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := δ) (c := 2 * Real.pi - δ) (μ := volume)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
      have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := 2 * Real.pi - δ) (c := 2 * Real.pi) (μ := volume)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
      linarith
    -- the dominating integral
    have hdom : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        3 * (‖f θ - hh θ‖ ^ 2 + Cb ^ 2 * (1 - χ θ) + η ^ 2)) ≤ ε := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hAint.add hBint) hCint,
        intervalIntegral.integral_add hAint hBint,
        show (fun θ : ℝ => Cb ^ 2 * (1 - χ θ)) = (fun θ : ℝ => Cb ^ 2 * (1 - χ θ)) from rfl,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      have hCb2 : Cb ^ 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), (1 - χ θ)) ≤ ε / 9 := by
        refine le_trans (mul_le_mul_of_nonneg_left hB (by positivity)) hδbound
      have hηb : (2 * Real.pi - 0) • η ^ 2 ≤ ε / 9 := by
        have hpne : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
        have heq : (2 * Real.pi - 0) * (ε / (9 * (2 * Real.pi))) = ε / 9 := by
          field_simp
          ring
        rw [smul_eq_mul, hηsq, heq]
      linarith
    exact le_trans (intervalIntegral.integral_mono_on h2pi.le hfTint
      ((hAint.add hBint).add hCint |>.const_mul 3) hptb) hdom
  -- ## the conclusion
  rw [show (fun m : ℤ => 2 * Real.pi *
      ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        f θ * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
      = (fun m : ℤ => 2 * Real.pi * ‖cc m‖ ^ 2) from funext (fun m => by rw [hccgoal m])]
  refine hasSum_of_isLUB_of_nonneg _ (fun m => by positivity) ?_
  constructor
  · rintro x ⟨s, rfl⟩
    have h1 := hbessel s
    have h2 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ - ∑ j ∈ s, cc j * ee j θ‖ ^ 2 :=
      intervalIntegral.integral_nonneg h2pi.le (fun u _ => by positivity)
    have h3 : ∑ m ∈ s, 2 * Real.pi * ‖cc m‖ ^ 2 = 2 * Real.pi * ∑ j ∈ s, ‖cc j‖ ^ 2 :=
      (Finset.mul_sum s (fun j => ‖cc j‖ ^ 2) (2 * Real.pi)).symm
    simp only []
    rw [h3]
    linarith
  · intro y hy
    rcases le_or_gt (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ‖ ^ 2) y with hle | hgt
    · exact hle
    · exfalso
      obtain ⟨s, b, hsb⟩ := happrox
        (((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖f θ‖ ^ 2) - y) / 2) (by linarith)
      have h1 := hbessel s
      have h2 := hbest s b
      have h3 : ∑ m ∈ s, 2 * Real.pi * ‖cc m‖ ^ 2 = 2 * Real.pi * ∑ j ∈ s, ‖cc j‖ ^ 2 :=
        (Finset.mul_sum s (fun j => ‖cc j‖ ^ 2) (2 * Real.pi)).symm
      have h4 : ∑ m ∈ s, 2 * Real.pi * ‖cc m‖ ^ 2 ≤ y := hy ⟨s, rfl⟩
      rw [h3] at h4
      linarith
