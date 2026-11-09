import IwaniecManfredi.Preamble
import Mathlib.Analysis.SpecialFunctions.PolarCoord
set_option maxHeartbeats 1000000

open MeasureTheory

/-- The polar evaluation of the Dirichlet-type energy of a function on the
unit disc: for every measurable `f : ℂ → ℂ`,
`∫⁻_{0<r<1} r ∫⁻_{0<θ<2π} ‖f(r e^{iθ})‖² = ∫⁻_{‖ξ‖<1} ‖f(ξ)‖²`,
as integrals in `ℝ≥0∞`, with the Jacobian factor `r` of the polar map on the
left and plane Lebesgue measure on the right.

This is the first move of the energy computation of Section 4
(`paper.tex:353-357`), where the area integral of `|H_r|²` over the unit disc
is rewritten as `∫_0^1 r ∫_0^{2π} |H_r|² dθ dr` before Parseval is applied to
the inner integral.  Stating it for an arbitrary measurable `f`, in the
`ℝ≥0∞`-valued Lebesgue integral, is what makes it usable on each of the three
functions `H`, `H_ξ` and `H_ξ̄` without any integrability hypothesis: no
finiteness is assumed or asserted, and both sides are `⊤` together when the
energy is infinite.

The angular window is `(0, 2π)` rather than Mathlib's `(-π, π)`, because that
is the window in which the Fourier computation of Section 4 is carried out;
moving between the two is part of the proof. -/
theorem DiscEnergyPolarCoord (f : ℂ → ℂ) (hf : Measurable f) :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r
        * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
      = ∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖f ξ‖ ^ 2) := by
  -- the two ambient facts the block used from its old surroundings
  have hBdmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hcircnorm : ∀ (r : ℝ), 0 < r → ∀ θ : ℝ,
      ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
    intro r hr θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hcimem : ∀ (s θ : ℝ), 0 < s → s < 1 →
      ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro s θ hs hs1
    show ‖_‖ < 1
    rw [hcircnorm s hs θ]
    exact hs1
  have hcisymm : ∀ q : ℝ × ℝ, (Complex.polarCoord.symm q)
      = ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)) := by
    intro q
    rw [Complex.polarCoord_symm_apply]
    simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hrot : ∀ (s θ : ℝ), -((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((s : ℂ) * Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I)) := by
    intro s θ
    rw [show (((θ + Real.pi : ℝ) : ℂ)) * Complex.I
        = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hcicont : Continuous
      (fun q : ℝ × ℝ => ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))) := by fun_prop
  have hmemsh : ∀ θ : ℝ,
      (θ ∈ Set.Ioo (-Real.pi) Real.pi ↔ θ + Real.pi ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
    intro θ
    constructor
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨FF, hFFval⟩ : ∃ G : ℂ → ENNReal, ∀ ζ : ℂ,
      G ζ = Set.indicator {ξ : ℂ | ‖ξ‖ < 1} (fun ξ => ENNReal.ofReal (‖f ξ‖ ^ 2)) ζ :=
    ⟨_, fun _ => rfl⟩
  have hFFfun : FF = fun ζ => Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
      (fun ξ => ENNReal.ofReal (‖f ξ‖ ^ 2)) ζ := funext hFFval
  have hFFm : Measurable FF := by
    rw [hFFfun]
    exact (ENNReal.measurable_ofReal.comp ((hf.norm).pow_const 2)).indicator hBdmeas
  have hpol := Complex.lintegral_comp_polarCoord_symm (fun ζ => FF (-ζ))
  rw [MeasureTheory.lintegral_neg_eq_self FF,
    show (polarCoord.target : Set (ℝ × ℝ))
      = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl] at hpol
  simp only [hcisymm, smul_eq_mul] at hpol
  have hmeas2 : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal q.1 * FF (-((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hFFm.comp (continuous_neg.measurable.comp hcicont.measurable))
  have hton : (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal q.1 * FF (-((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.lintegral_prod _ hmeas2.aemeasurable
  have htr : ∀ r : ℝ, (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
        FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro r
    have h1 : ∀ θ : ℝ, Set.indicator (Set.Ioo (-Real.pi) Real.pi)
          (fun θ => FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) θ
        = Set.indicator (Set.Ioo (0 : ℝ) (2 * Real.pi))
          (fun θ => FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (θ + Real.pi) := by
      intro θ
      by_cases h : θ ∈ Set.Ioo (-Real.pi) Real.pi
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmemsh θ).mp h), hrot]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun hc => h ((hmemsh θ).mpr hc))]
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioo,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioo,
      MeasureTheory.lintegral_congr h1]
    exact MeasureTheory.lintegral_add_right_eq_self
      (Set.indicator (Set.Ioo (0 : ℝ) (2 * Real.pi))
        (fun θ => FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) Real.pi
  have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r
        * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      = ∫⁻ ζ : ℂ, FF ζ := by
    rw [← hpol, hton]
    refine MeasureTheory.lintegral_congr (fun r => ?_)
    rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal r ≠ ⊤), htr r]
  rw [MeasureTheory.lintegral_indicator hBdmeas (f := fun ξ =>
    ENNReal.ofReal (‖f ξ‖ ^ 2)) |>.symm]
  rw [show (fun ζ : ℂ => Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
      (fun ξ => ENNReal.ofReal (‖f ξ‖ ^ 2)) ζ) = FF from hFFfun.symm]
  rw [← hstep, ← MeasureTheory.lintegral_indicator measurableSet_Ioo,
    ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
  refine MeasureTheory.lintegral_congr (fun r => ?_)
  by_cases h1 : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ioi.mpr h1.1)]
    congr 1
    refine MeasureTheory.lintegral_congr (fun θ => ?_)
    rw [hFFval, Set.indicator_of_mem (hcimem r θ h1.1 h1.2)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : r ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h2]
      have hr0 : (0 : ℝ) < r := h2
      have hr1 : (1 : ℝ) ≤ r := by
        rcases lt_or_ge r 1 with h | h
        · exact absurd (Set.mem_Ioo.mpr ⟨hr0, h⟩) h1
        · exact h
      have hzfun : ∀ θ : ℝ, FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
        intro θ
        have hnm : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∉ {ξ : ℂ | ‖ξ‖ < 1} := by
          intro hc
          have hcc : ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ < 1 := hc
          rw [hcircnorm r hr0 θ] at hcc
          linarith
        rw [hFFval, Set.indicator_of_notMem hnm]
      rw [MeasureTheory.lintegral_congr hzfun, MeasureTheory.lintegral_zero, mul_zero]
    · rw [Set.indicator_of_notMem h2]
