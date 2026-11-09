import IwaniecManfredi.FourierCoefOfH
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option maxHeartbeats 1600000

open MeasureTheory

/-- The two measure-theoretic properties of the Fourier coefficient
`FourierCoefOfH n F k` of a plane function, read as a function of the radius on
a compact annulus `c' ≤ |ζ| ≤ d'` with `c' > 0`:

* (a) if `W` is measurable and integrable on the annulus, then its coefficient
  is integrable in the radius over `(c', d')`, and for almost every radius `s`
  in that interval the circle restriction `θ ↦ W(s e^{iθ})` is
  interval-integrable over a full period;
* (b) the coefficient depends continuously on the function in `L¹`: if
  `Fs l → F` in `L¹(ℂ)`, then
  `∫⁻_{(c',d')} ‖(Fs l)^_k(s) - F^_k(s)‖ → 0`.

Both are properties of the same operator `F ↦ FourierCoefOfH n F k`, which is
why they are stated together: (b) is proved from (a), and the proof of (a) is
what makes the inner integral defining the coefficient meaningful in the first
place.

This is the measure-theoretic foundation under the circle-average argument.
The paper reads `a_k ∈ C[0,1) ∩ C^∞(0,1)` off its standing smoothness
hypothesis at `paper.tex:265-266`; the tablet has no such hypothesis and
replaces that step by `CircleAvgLocAbsCont`, which needs these two facts
before it can start -- (a) to know that the coefficient is a genuine
integrable function of the radius, and (b) to pass to the limit in a
mollification, where the approximating functions converge to `W` only in
`L¹`.

The positive inner radius `c' > 0` is essential and is used twice: it keeps the
Jacobian of the polar map bounded below on the annulus, which is what turns an
`L¹` bound on the plane into an `L¹` bound in the polar variables, and it
bounds the factor `1/s` in the pointwise estimate behind (b). -/
theorem FourierCoefAnnulusRegularity (n : ℕ) (k : ℤ) (c' d' : ℝ) (hc' : 0 < c') :
    (∀ W : ℂ → ℂ, Measurable W →
      IntegrableOn W {ζ : ℂ | c' ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ d'} volume →
      IntegrableOn (FourierCoefOfH n W k) (Set.Ioo c' d') volume ∧
      (∀ᵐ s : ℝ, s ∈ Set.Ioo c' d' →
        IntervalIntegrable
          (fun θ : ℝ => W ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          volume 0 (2 * Real.pi)))
    ∧ (∀ (Fs : ℕ → ℂ → ℂ) (F : ℂ → ℂ),
      (∀ l, Measurable (Fs l)) → Measurable F →
      (∀ l, Integrable (Fs l) volume) → Integrable F volume →
      Filter.Tendsto (fun l => ∫ ζ, ‖Fs l ζ - F ζ‖) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun l => (∫⁻ s in Set.Ioo c' d',
          ‖FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s‖ₑ))
        Filter.atTop (nhds 0)) := by
  -- the circle parametrisation, the angular weight, the polar change of
  -- variables, the window change to `Ioo (-π) π`, and the compact annulus
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
  have hwtne : ∀ θ : ℝ, wt θ ≠ 0 := fun θ => by
    rw [hwtdef]
    exact Complex.exp_ne_zero _
  -- measurability of the two polar derivatives
  have hcisymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = ci p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, hcidef]
    simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hpolar : ∀ G : ℂ → ENNReal,
      (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * G (ci p.1 p.2)) = ∫⁻ ζ, G ζ := by
    intro G
    have h := Complex.lintegral_comp_polarCoord_symm G
    rw [show (polarCoord.target : Set (ℝ × ℝ))
        = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl] at h
    simp only [hcisymm, smul_eq_mul] at h
    exact h
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
  -- the Fourier coefficient written over a full period, and its angular periodicity
  have hFC : ∀ (F : ℂ → ℂ) (s : ℝ), FourierCoefOfH n F k s
      = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), F (ci s θ) * wt θ := by
    intro F s
    rw [FourierCoefOfH, hcidef, hwtdef]
  have hperm : ∀ (F : ℂ → ℂ) (s : ℝ),
      Function.Periodic (fun θ : ℝ => F (ci s θ) * wt θ) (2 * Real.pi) := by
    intro F s θ
    simp only
    rw [hperci s θ, hperwt θ]
  have hpilt : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hIoo : ∀ (F : ℂ → ℂ) (s : ℝ),
      (∫ θ in (0 : ℝ)..(2 * Real.pi), F (ci s θ) * wt θ)
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi, F (ci s θ) * wt θ := by
    intro F s
    have h1 := (hperm F s).intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add] at h1
    rw [h1, show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le hpilt, integral_Ioc_eq_integral_Ioo]
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
  have hAnnmeas : ∀ c' d' : ℝ, MeasurableSet (Ann c' d') :=
    fun c' d' => (hAnncomp c' d').measurableSet
  have hlkey : ∀ (c' d' : ℝ), 0 < c' → ∀ F : ℂ → ℂ,
      ENNReal.ofReal c' *
        (∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖F (ci p.1 p.2)‖ₑ)
          ≤ ∫⁻ ζ, ‖F ζ‖ₑ := by
    intro c' d' hc' F
    have hmset : MeasurableSet (Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioo.prod measurableSet_Ioo
    calc ENNReal.ofReal c' *
          (∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖F (ci p.1 p.2)‖ₑ)
        = ∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal c' * ‖F (ci p.1 p.2)‖ₑ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 * ‖F (ci p.1 p.2)‖ₑ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hmset).mpr
            (Filter.Eventually.of_forall fun p hp => ?_))
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_lt hp.1.1)) le_rfl
      _ ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 * ‖F (ci p.1 p.2)‖ₑ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          exact Set.prod_mono (fun x hx => lt_of_lt_of_le hc' (le_of_lt hx.1)) le_rfl
      _ = ∫⁻ ζ, ‖F ζ‖ₑ := hpolar (fun ζ => ‖F ζ‖ₑ)
  -- the master product-integrability statement
  have hprod : ∀ (c' d' : ℝ), 0 < c' → ∀ F : ℂ → ℂ, Measurable F → Integrable F volume →
      Integrable (fun p : ℝ × ℝ => F (ci p.1 p.2) * wt p.2)
        ((volume.restrict (Set.Ioo c' d')).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    intro c' d' hc' F hFm hFi
    have hmeas : Measurable (fun p : ℝ × ℝ => F (ci p.1 p.2) * wt p.2) :=
      (hFm.comp hcicont.measurable).mul (hwtcont.measurable.comp measurable_snd)
    refine ⟨hmeas.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    have hmset : MeasurableSet (Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioo.prod measurableSet_Ioo
    have hmeq : (volume.restrict (Set.Ioo c' d')).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))
        = (volume : Measure (ℝ × ℝ)).restrict
            (Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hnorm : ∀ p : ℝ × ℝ, ‖F (ci p.1 p.2) * wt p.2‖ₑ = ‖F (ci p.1 p.2)‖ₑ := by
      intro p
      rw [enorm_mul, show ‖wt p.2‖ₑ = 1 by rw [← ofReal_norm, hwtnorm, ENNReal.ofReal_one],
        mul_one]
    have hkey := hlkey c' d' hc' F
    have hFtop : (∫⁻ ζ, ‖F ζ‖ₑ) ≠ ⊤ := hFi.2.ne
    have hlt : (∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖F (ci p.1 p.2)‖ₑ) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero]; linarith)] at hkey
      exact hFtop (top_le_iff.mp hkey)
    rw [HasFiniteIntegral, hmeq]
    simp only [hnorm]
    exact lt_of_le_of_ne le_top hlt
  -- the local form of (a) and (e), for a measurable function integrable on the annulus
  have hgen : ∀ (c' d' : ℝ), 0 < c' → ∀ W : ℂ → ℂ, Measurable W →
      IntegrableOn W (Ann c' d') volume →
      IntegrableOn (FourierCoefOfH n W k) (Set.Ioo c' d') volume ∧
      (∀ᵐ s : ℝ, s ∈ Set.Ioo c' d' →
        IntervalIntegrable (fun θ : ℝ => W (ci s θ)) volume 0 (2 * Real.pi)) := by
    intro c' d' hc' W hWm hWi
    set F : ℂ → ℂ := (Ann c' d').indicator W with hFdef
    have hFm : Measurable F := hWm.indicator (hAnnmeas c' d')
    have hFi : Integrable F volume := (integrable_indicator_iff (hAnnmeas c' d')).mpr hWi
    have hFeq : ∀ s : ℝ, s ∈ Set.Ioo c' d' → ∀ θ : ℝ, F (ci s θ) = W (ci s θ) := by
      intro s hs θ
      rw [hFdef]
      refine Set.indicator_of_mem ?_ W
      rw [hAnnmem, hcinorm s θ, abs_of_pos (lt_trans hc' hs.1)]
      exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hP := hprod c' d' hc' F hFm hFi
    have h2πne : (2 * Real.pi) ≠ 0 := by positivity
    constructor
    · have h1 := hP.integral_prod_left
      have h2 : IntegrableOn
          (fun s => (1 / (2 * Real.pi) : ℂ) *
            ∫ θ in Set.Ioo (-Real.pi) Real.pi, F (ci s θ) * wt θ)
          (Set.Ioo c' d') volume := h1.const_mul _
      refine h2.congr_fun ?_ measurableSet_Ioo
      intro s hs
      show (1 / (2 * Real.pi) : ℂ) *
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, F (ci s θ) * wt θ) = FourierCoefOfH n W k s
      rw [hFC, hIoo]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro θ _
      show F (ci s θ) * wt θ = W (ci s θ) * wt θ
      rw [hFeq s hs θ]
    · have h3 := hP.prod_right_ae
      rw [ae_restrict_iff' measurableSet_Ioo] at h3
      filter_upwards [h3] with s hs3 hs
      have hs4 : IntegrableOn (fun θ : ℝ => F (ci s θ) * wt θ)
          (Set.Ioo (-Real.pi) Real.pi) volume := hs3 hs
      have hcong : Set.EqOn (fun θ : ℝ => F (ci s θ) * wt θ)
          (fun θ : ℝ => W (ci s θ) * wt θ) (Set.Ioo (-Real.pi) Real.pi) := by
        intro θ _
        show F (ci s θ) * wt θ = W (ci s θ) * wt θ
        rw [hFeq s hs θ]
      have h4 : IntegrableOn (fun θ : ℝ => W (ci s θ) * wt θ)
          (Set.Ioo (-Real.pi) Real.pi) volume := hs4.congr_fun hcong measurableSet_Ioo
      have h5 : IntervalIntegrable (fun θ : ℝ => W (ci s θ) * wt θ) volume
          (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
          intervalIntegrable_iff_integrableOn_Ioo_of_le hpilt]
        exact h4
      have h6 : IntervalIntegrable (fun θ : ℝ => W (ci s θ) * wt θ) volume 0 (2 * Real.pi) :=
        (hperm W s).intervalIntegrable h2πne h5 0 (2 * Real.pi)
      have h7 : IntervalIntegrable (fun θ : ℝ => (W (ci s θ) * wt θ) * (wt θ)⁻¹)
          volume 0 (2 * Real.pi) :=
        h6.mul_continuousOn ((hwtcont.inv₀ hwtne).continuousOn)
      have heq2 : (fun θ : ℝ => (W (ci s θ) * wt θ) * (wt θ)⁻¹) = fun θ : ℝ => W (ci s θ) := by
        funext θ
        rw [mul_assoc, mul_inv_cancel₀ (hwtne θ), mul_one]
      rw [heq2] at h7
      exact h7
  -- the `L¹` continuity of the Fourier coefficient in its function argument
  have hwtenorm : ∀ θ : ℝ, ‖wt θ‖ₑ = 1 := by
    intro θ
    rw [← ofReal_norm, hwtnorm, ENNReal.ofReal_one]
  have hwte : ∀ (z : ℂ) (θ : ℝ), ‖z * wt θ‖ₑ = ‖z‖ₑ := by
    intro z θ
    rw [enorm_mul, hwtenorm θ, mul_one]
  have hconstnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ₑ = ENNReal.ofReal (1 / (2 * Real.pi)) := by
    rw [← ofReal_norm]
    congr 1
    rw [norm_div, norm_one,
      show ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hFCconv : ∀ (c' d' : ℝ), 0 < c' → ∀ (Fs : ℕ → ℂ → ℂ) (F : ℂ → ℂ),
      (∀ l, Measurable (Fs l)) → Measurable F →
      (∀ l, Integrable (Fs l) volume) → Integrable F volume →
      Filter.Tendsto (fun l => ∫ ζ, ‖Fs l ζ - F ζ‖) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun l => (∫⁻ s in Set.Ioo c' d',
          ‖FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s‖ₑ))
        Filter.atTop (nhds 0) := by
    intro c' d' hc' Fs F hFsm hFm hFsi hFi htend
    have hc'0 : ENNReal.ofReal c' ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hc'
    have hbnd : ∀ l : ℕ, (∫⁻ s in Set.Ioo c' d',
        ‖FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s‖ₑ)
          ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ((ENNReal.ofReal c')⁻¹ *
              ENNReal.ofReal (∫ ζ, ‖Fs l ζ - F ζ‖)) := by
      intro l
      set Gl : ℂ → ℂ := fun ζ => Fs l ζ - F ζ with hGldef
      have hGlm : Measurable Gl := by
        rw [hGldef]; exact (hFsm l).sub hFm
      have hGli : Integrable Gl volume := by
        rw [hGldef]; exact (hFsi l).sub hFi
      have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioo c' d')),
          ‖FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s‖ₑ
            ≤ ENNReal.ofReal (1 / (2 * Real.pi)) *
                ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci s θ)‖ₑ := by
        filter_upwards [(hprod c' d' hc' (Fs l) (hFsm l) (hFsi l)).prod_right_ae,
          (hprod c' d' hc' F hFm hFi).prod_right_ae] with s hs1 hs2
        have hint1 : IntegrableOn (fun θ : ℝ => Fs l (ci s θ) * wt θ)
            (Set.Ioo (-Real.pi) Real.pi) volume := hs1
        have hint2 : IntegrableOn (fun θ : ℝ => F (ci s θ) * wt θ)
            (Set.Ioo (-Real.pi) Real.pi) volume := hs2
        have hdiff : FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s
            = (1 / (2 * Real.pi) : ℂ) *
              ∫ θ in Set.Ioo (-Real.pi) Real.pi, Gl (ci s θ) * wt θ := by
          rw [hFC (Fs l) s, hFC F s, hIoo (Fs l) s, hIoo F s, ← mul_sub,
            ← integral_sub hint1 hint2]
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioo ?_
          intro θ _
          show Fs l (ci s θ) * wt θ - F (ci s θ) * wt θ = Gl (ci s θ) * wt θ
          rw [hGldef]
          ring
        rw [hdiff, enorm_mul, hconstnorm]
        refine mul_le_mul' le_rfl ?_
        refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
        exact lintegral_congr fun θ => hwte (Gl (ci s θ)) θ
      have htonelli : (∫⁻ s in Set.Ioo c' d', ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ‖Gl (ci s θ)‖ₑ)
          = ∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci p.1 p.2)‖ₑ := by
        have hmeq : (volume.restrict (Set.Ioo c' d')).prod
            (volume.restrict (Set.Ioo (-Real.pi) Real.pi))
            = (volume : Measure (ℝ × ℝ)).restrict
                (Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        have hm : AEMeasurable (fun p : ℝ × ℝ => ‖Gl (ci p.1 p.2)‖ₑ)
            ((volume.restrict (Set.Ioo c' d')).prod
              (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) :=
          ((hGlm.comp hcicont.measurable).enorm).aemeasurable
        rw [← hmeq, lintegral_prod _ hm]
      have hX : (∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci p.1 p.2)‖ₑ)
          ≤ (ENNReal.ofReal c')⁻¹ * ∫⁻ ζ, ‖Gl ζ‖ₑ := by
        calc (∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci p.1 p.2)‖ₑ)
            = (ENNReal.ofReal c')⁻¹ * (ENNReal.ofReal c' *
                ∫⁻ p in Set.Ioo c' d' ×ˢ Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci p.1 p.2)‖ₑ) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hc'0 ENNReal.ofReal_ne_top, one_mul]
          _ ≤ (ENNReal.ofReal c')⁻¹ * ∫⁻ ζ, ‖Gl ζ‖ₑ :=
              mul_le_mul' le_rfl (hlkey c' d' hc' Gl)
      have hY : (∫⁻ ζ, ‖Gl ζ‖ₑ) = ENNReal.ofReal (∫ ζ, ‖Fs l ζ - F ζ‖) := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hGli]
      calc (∫⁻ s in Set.Ioo c' d',
            ‖FourierCoefOfH n (Fs l) k s - FourierCoefOfH n F k s‖ₑ)
          ≤ ∫⁻ s in Set.Ioo c' d', ENNReal.ofReal (1 / (2 * Real.pi)) *
              ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci s θ)‖ₑ := lintegral_mono_ae hae
        _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ s in Set.Ioo c' d',
              ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ‖Gl (ci s θ)‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ((ENNReal.ofReal c')⁻¹ *
              ENNReal.ofReal (∫ ζ, ‖Fs l ζ - F ζ‖)) := by
            refine mul_le_mul' le_rfl ?_
            rw [htonelli, ← hY]
            exact hX
    have hR : Filter.Tendsto (fun l => ENNReal.ofReal (∫ ζ, ‖Fs l ζ - F ζ‖))
        Filter.atTop (nhds 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp htend
      simp only [ENNReal.ofReal_zero] at h
      exact h
    have hR2 : Filter.Tendsto (fun l => ENNReal.ofReal (1 / (2 * Real.pi)) *
        ((ENNReal.ofReal c')⁻¹ * ENNReal.ofReal (∫ ζ, ‖Fs l ζ - F ζ‖)))
        Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := (ENNReal.ofReal c')⁻¹) hR
        (Or.inr (ENNReal.inv_ne_top.mpr hc'0))
      rw [mul_zero] at h1
      have h2 := ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal (1 / (2 * Real.pi))) h1 (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at h2
      exact h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR2
      (Filter.Eventually.of_forall fun _ => zero_le)
      (Filter.Eventually.of_forall hbnd)
  exact ⟨hgen c' d' hc', hFCconv c' d' hc'⟩
