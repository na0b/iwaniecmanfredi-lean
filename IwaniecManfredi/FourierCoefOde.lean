import IwaniecManfredi.FourierCoefRegularity
import IwaniecManfredi.PolarEq28
import IwaniecManfredi.LinearOdeSystemSmooth
import Mathlib.Analysis.Calculus.Deriv.Star

/-- The system (33) of Section 4 of the paper for the Fourier coefficients of a
`W^{1,2}` solution of (18), the regularity (31) of those coefficients, and the
uncoupled second-order equation (35).  The intermediate elimination (34) is
carried out inside the proof, since nothing else uses it.

Section 3's `C^∞` standing assumption is *not* a hypothesis: `paper.tex:265-266`
reads it only to get `a_k ∈ C^∞(0,1)`, and that is obtained here instead from
the system itself, through `LinearOdeSystemSmooth` applied to the closed pair
`(a_k, conj a_{-k})` -- which is why the smoothness of the coefficients is a
*conclusion* of this node.  With it, (33) upgrades from almost every `r` to
every `r`, so the three conclusions are exactly what the rest of Section 4
already consumed. -/
theorem FourierCoefOde (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (H : ℂ → ℂ)
    (hc : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1})
    (hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H)
    (hdiff : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ)
    (h18 : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H) :
    (∀ (k : ℤ) (r : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 →
      2 * ((r : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) r
        = -(p : ℂ) * ((((n : ℤ) - k : ℤ) : ℤ) : ℂ) * FourierCoefOfH n H k r
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ) : ℤ) : ℂ)
              * starRingEnd ℂ (FourierCoefOfH n H (-k) r)) ∧
    (∀ (k : ℤ) (r : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 →
      ((r : ℝ) : ℂ) * deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) s) r
        + ((p * (n : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) r
        + ((((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) : ℝ) : ℂ) * FourierCoefOfH n H k r
        = 0) ∧
    (∀ k : ℤ, ContDiffOn ℝ (⊤ : ℕ∞) (FourierCoefOfH n H k) (Set.Ioo (0 : ℝ) 1)) := by
  classical
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  -- ## Notation
  set ci : ℝ → ℝ → ℂ := fun s θ => ((s : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
    with hcidef
  set wt : ℤ → ℝ → ℂ := fun j θ =>
    Complex.exp (((((n : ℤ) - j : ℤ)) : ℂ) * ((θ : ℝ) : ℂ) * Complex.I) with hwtdef
  have hcicont : Continuous (fun q : ℝ × ℝ => ci q.1 q.2) := by rw [hcidef]; fun_prop
  have hwtcont : ∀ j : ℤ, Continuous (wt j) := by intro j; rw [hwtdef]; fun_prop
  have hFC : ∀ (F : ℂ → ℂ) (j : ℤ) (s : ℝ), FourierCoefOfH n F j s
      = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), F (ci s θ) * wt j θ := by
    intro F j s
    rw [FourierCoefOfH, hcidef, hwtdef]
  have hcinorm : ∀ (s θ : ℝ), 0 ≤ s → ‖ci s θ‖ = s := by
    intro s θ hs
    rw [hcidef]
    simp only
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs]
  have hcine : ∀ (s θ : ℝ), 0 < s → ci s θ ≠ 0 := by
    intro s θ hs h
    have := hcinorm s θ hs.le
    rw [h] at this
    simp at this
    linarith
  -- ## conjugation: integrability and the interval integral
  have hconjon : ∀ (F : ℝ → ℂ) (s : Set ℝ),
      MeasureTheory.IntegrableOn F s MeasureTheory.volume →
      MeasureTheory.IntegrableOn (fun θ => starRingEnd ℂ (F θ)) s MeasureTheory.volume := by
    intro F s h
    refine MeasureTheory.Integrable.mono h ?_ (Filter.Eventually.of_forall (fun θ => by simp))
    exact Complex.continuous_conj.comp_aestronglyMeasurable h.1
  have hconjint : ∀ (F : ℝ → ℂ) (u v : ℝ),
      IntervalIntegrable F MeasureTheory.volume u v →
      IntervalIntegrable (fun θ => starRingEnd ℂ (F θ)) MeasureTheory.volume u v := by
    intro F u v h
    exact ⟨hconjon F _ h.1, hconjon F _ h.2⟩
  have hivconj : ∀ (F : ℝ → ℂ) (u v : ℝ),
      (∫ θ in u..v, starRingEnd ℂ (F θ)) = starRingEnd ℂ (∫ θ in u..v, F θ) := by
    intro F u v
    simp only [intervalIntegral, map_sub]
    rw [← integral_conj, ← integral_conj]
  -- ## the polar almost-everywhere transfer
  have hstageA : ∀ (N : Set ℂ), MeasurableSet N → MeasureTheory.volume N = 0 →
      ∀ᵐ s : ℝ, 0 < s → ∀ᵐ θ : ℝ, θ ∈ Set.Ioo (-Real.pi) Real.pi → ci s θ ∉ N := by
    intro N hNm hN0
    have hcisymm : ∀ q : ℝ × ℝ, (Complex.polarCoord.symm q) = ci q.1 q.2 := by
      intro q
      rw [Complex.polarCoord_symm_apply, hcidef]
      simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have hindm : Measurable (fun ζ : ℂ => N.indicator (fun _ => (1 : ENNReal)) ζ) :=
      measurable_const.indicator hNm
    have hlint : (∫⁻ ζ : ℂ, N.indicator (fun _ => (1 : ENNReal)) ζ) = 0 := by
      rw [MeasureTheory.lintegral_indicator hNm, MeasureTheory.setLIntegral_one, hN0]
    have hpol := Complex.lintegral_comp_polarCoord_symm
      (fun ζ => N.indicator (fun _ => (1 : ENNReal)) ζ)
    rw [hlint] at hpol
    simp only [hcisymm, smul_eq_mul] at hpol
    rw [show (polarCoord.target : Set (ℝ × ℝ))
        = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl] at hpol
    have hmeas : Measurable (fun q : ℝ × ℝ =>
        ENNReal.ofReal q.1 * N.indicator (fun _ => (1 : ENNReal)) (ci q.1 q.2)) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul (hindm.comp hcicont.measurable)
    have hae := (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hpol
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict] at hae
    have hae' : ∀ᵐ q : ℝ × ℝ
        ∂((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
          (MeasureTheory.volume.restrict (Set.Ioo (-Real.pi) Real.pi))),
        ENNReal.ofReal q.1 * N.indicator (fun _ => (1 : ENNReal)) (ci q.1 q.2) = 0 := hae
    have h2 := MeasureTheory.Measure.ae_ae_of_ae_prod hae'
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h2
    filter_upwards [h2] with s hs hs0
    have h3 := hs (Set.mem_Ioi.mpr hs0)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at h3
    filter_upwards [h3] with θ hθ hθmem
    have h4 := hθ hθmem
    have hsne : ENNReal.ofReal s ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hs0
    have h5 : N.indicator (fun _ => (1 : ENNReal)) (ci s θ) = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h hsne
      · exact h
    intro hmemN
    rw [Set.indicator_of_mem hmemN] at h5
    exact one_ne_zero h5
  have hrotci : ∀ (s θ : ℝ), ci s (θ + Real.pi) = -(ci s θ) := by
    intro s θ
    rw [hcidef]
    simp only
    rw [show (((θ + Real.pi : ℝ)) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I
        from by push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hpolarae : ∀ (Q : ℂ → Prop), (∀ᵐ ξ : ℂ, Q ξ) →
      ∀ᵐ s : ℝ, 0 < s → ∀ᵐ θ : ℝ, θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) → Q (ci s θ) := by
    intro Q hQ
    obtain ⟨N, hsub, hNm, hN0⟩ :=
      MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hQ)
    have hNn0 : MeasureTheory.volume (-N : Set ℂ) = 0 := by
      rw [show ((-N : Set ℂ)) = (Neg.neg) ⁻¹' N from rfl,
        MeasureTheory.Measure.measure_preimage_neg]
      exact hN0
    have hA := hstageA (-N) hNm.neg hNn0
    have hne : ∀ᵐ θ : ℝ, θ ≠ 2 * Real.pi := by
      refine (MeasureTheory.ae_iff).mpr ?_
      simp
    filter_upwards [hA] with s hs hs0
    have h1 := hs hs0
    have h1' : ∀ᵐ φ : ℝ, φ ∈ Set.Ioo (-Real.pi) Real.pi → Q (ci s (φ + Real.pi)) := by
      filter_upwards [h1] with φ hφ hφmem
      have hnotin : ci s φ ∉ (-N : Set ℂ) := hφ hφmem
      have : -(ci s φ) ∉ N := by
        intro hmem
        exact hnotin (by rwa [Set.mem_neg])
      rw [hrotci]
      by_contra hQc
      exact this (hsub hQc)
    have h2 := (MeasureTheory.measurePreserving_sub_right
      MeasureTheory.volume Real.pi).quasiMeasurePreserving.ae h1'
    filter_upwards [h2, hne] with θ hθ hθne hθmem
    have hmem' : θ - Real.pi ∈ Set.Ioo (-Real.pi) Real.pi :=
      ⟨by linarith [hθmem.1], by
        have := lt_of_le_of_ne hθmem.2 hθne
        linarith⟩
    have := hθ hmem'
    rwa [show θ - Real.pi + Real.pi = θ from by ring] at this
  -- ## Step 1: the coefficient identities
  obtain ⟨h1a, h1b, h1c, h1d, h1e, h1f⟩ := FourierCoefRegularity n H hc hw hdiff
  -- ## Step 2: equation (28) on circles
  have h28 := PolarEq28 n p hn hp {ξ : ℂ | ‖ξ‖ < 1} hBopen H hdiff h18
  set er : ℝ → ℂ := fun θ =>
    Complex.exp ((((-2 * (n : ℤ) : ℤ)) : ℂ) * ((θ : ℝ) : ℂ) * Complex.I) with herdef
  have hconjci : ∀ (s θ : ℝ),
      starRingEnd ℂ (ci s θ) = ((s : ℝ) : ℂ) * Complex.exp (-(((θ : ℝ) : ℂ) * Complex.I)) := by
    intro s θ
    rw [hcidef]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [Complex.conj_I]
    ring
  have hpow : ∀ (s θ : ℝ), 0 < s →
      ((starRingEnd ℂ (ci s θ)) / (ci s θ)) ^ n = er θ := by
    intro s θ hs
    have hs0 : ((s : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hs
    rw [hconjci, hcidef]
    simp only
    rw [mul_div_mul_left _ _ hs0, ← Complex.exp_sub, ← Complex.exp_nat_mul, herdef]
    congr 1
    push_cast
    ring
  have hkey : ∀ (k : ℤ) (θ : ℝ), er θ * wt k θ = starRingEnd ℂ (wt (-k) θ) := by
    intro k θ
    rw [herdef, hwtdef]
    simp only [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- the polar form of (28), for almost every radius and almost every angle
  have heq3 : ∀ᵐ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → ∀ᵐ θ : ℝ,
      θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) →
      2 * ((s : ℝ) : ℂ) * HRad H (ci s θ)
        = -Complex.I * (p : ℂ) * HAng H (ci s θ)
          + ((p : ℂ) - 2) * Complex.I * er θ * starRingEnd ℂ (HAng H (ci s θ)) := by
    have hQ := hpolarae _ h28
    filter_upwards [hQ] with s hs hsmem
    obtain ⟨hs0, hs1⟩ := hsmem
    filter_upwards [hs hs0] with θ hθ hθmem
    have hmemB : ci s θ ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
      show ‖ci s θ‖ < 1
      rw [hcinorm s θ hs0.le]
      exact hs1
    have h := hθ hθmem hmemB (hcine s θ hs0)
    rw [hcinorm s θ hs0.le, hpow s θ hs0] at h
    exact h
  -- ## Step 3: the coefficient identity (4), off a null set
  have h4 : ∀ k : ℤ, ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      2 * ((r : ℝ) : ℂ) * FourierCoefOfH n (HRad H) k r
        = -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k r
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
              * starRingEnd ℂ (FourierCoefOfH n H (-k) r) := by
    intro k
    filter_upwards [heq3, h1d k, h1d (-k), h1e] with r hr3 hrdk hrdmk hre hrmem
    obtain ⟨hr0, hr1⟩ := hrmem
    have hrmem' : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hr1⟩
    have hHt := (hre hrmem').2
    have hI2 : IntervalIntegrable (fun θ => HAng H (ci r θ) * wt k θ)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      hHt.mul_continuousOn ((hwtcont k).continuousOn)
    have hI3 : IntervalIntegrable (fun θ => HAng H (ci r θ) * wt (-k) θ)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      hHt.mul_continuousOn ((hwtcont (-k)).continuousOn)
    have hG1 : IntervalIntegrable
        (fun θ => (-Complex.I * (p : ℂ)) * (HAng H (ci r θ) * wt k θ))
        MeasureTheory.volume 0 (2 * Real.pi) := hI2.const_mul _
    have hG2 : IntervalIntegrable
        (fun θ => (((p : ℂ) - 2) * Complex.I) * starRingEnd ℂ (HAng H (ci r θ) * wt (-k) θ))
        MeasureTheory.volume 0 (2 * Real.pi) := (hconjint _ _ _ hI3).const_mul _
    have hpt : ∀ᵐ θ : ℝ, θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
        (2 * ((r : ℝ) : ℂ) * HRad H (ci r θ)) * wt k θ
          = (-Complex.I * (p : ℂ)) * (HAng H (ci r θ) * wt k θ)
            + (((p : ℂ) - 2) * Complex.I) * starRingEnd ℂ (HAng H (ci r θ) * wt (-k) θ) := by
      filter_upwards [hr3 hrmem'] with θ hθ hθmem
      rw [Set.uIoc_of_le (le_of_lt h2pi)] at hθmem
      rw [hθ hθmem, map_mul, ← hkey k θ]
      ring
    have hstep : (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (2 * ((r : ℝ) : ℂ) * HRad H (ci r θ)) * wt k θ)
        = (-Complex.I * (p : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), HAng H (ci r θ) * wt k θ)
          + (((p : ℂ) - 2) * Complex.I)
              * starRingEnd ℂ (∫ θ in (0 : ℝ)..(2 * Real.pi), HAng H (ci r θ) * wt (-k) θ) := by
      rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_add hG1 hG2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hivconj]
    have hlhs : (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (2 * ((r : ℝ) : ℂ) * HRad H (ci r θ)) * wt k θ)
        = (2 * ((r : ℝ) : ℂ)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), HRad H (ci r θ) * wt k θ := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun θ _ => by ring)
    have hconjhalf : starRingEnd ℂ (1 / (2 * Real.pi) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by
      simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc 2 * ((r : ℝ) : ℂ) * FourierCoefOfH n (HRad H) k r
        = (1 / (2 * Real.pi) : ℂ) * ((2 * ((r : ℝ) : ℂ))
            * ∫ θ in (0 : ℝ)..(2 * Real.pi), HRad H (ci r θ) * wt k θ) := by
          rw [hFC]; ring
      _ = (1 / (2 * Real.pi) : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (2 * ((r : ℝ) : ℂ) * HRad H (ci r θ)) * wt k θ) := by rw [hlhs]
      _ = (1 / (2 * Real.pi) : ℂ) *
            ((-Complex.I * (p : ℂ))
                * (∫ θ in (0 : ℝ)..(2 * Real.pi), HAng H (ci r θ) * wt k θ)
              + (((p : ℂ) - 2) * Complex.I)
                * starRingEnd ℂ
                    (∫ θ in (0 : ℝ)..(2 * Real.pi), HAng H (ci r θ) * wt (-k) θ)) := by
          rw [hstep]
      _ = (-Complex.I * (p : ℂ)) * FourierCoefOfH n (HAng H) k r
            + (((p : ℂ) - 2) * Complex.I)
              * starRingEnd ℂ (FourierCoefOfH n (HAng H) (-k) r) := by
          rw [hFC (HAng H) k r, hFC (HAng H) (-k) r, map_mul, hconjhalf]
          ring
      _ = -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k r
            - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
                * starRingEnd ℂ (FourierCoefOfH n H (-k) r) := by
          rw [hrdk hrmem', hrdmk hrmem']
          simp only [map_mul, map_intCast, Complex.conj_I]
          push_cast
          linear_combination (-((p : ℂ) * ((k : ℂ) - (n : ℂ)) * FourierCoefOfH n H k r
            + ((p : ℂ) - 2) * (-(k : ℂ) - (n : ℂ))
              * starRingEnd ℂ (FourierCoefOfH n H (-k) r))) * hII
  -- ## Step 4: each coefficient is `C^∞` on `(0,1)`
  have hMsmooth : ∀ c : ℂ, ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => c / (2 * ((r : ℝ) : ℂ)))
      (Set.Ioo (0 : ℝ) 1) := by
    intro c
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => ((r : ℝ) : ℂ)) (Set.Ioo (0 : ℝ) 1) :=
      Complex.ofRealCLM.contDiff.contDiffOn
    have hden : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => (2 : ℂ) * ((r : ℝ) : ℂ))
        (Set.Ioo (0 : ℝ) 1) := contDiffOn_const.mul h1
    have hne : ∀ r ∈ Set.Ioo (0 : ℝ) 1, (2 : ℂ) * ((r : ℝ) : ℂ) ≠ 0 := by
      intro r hr
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨by norm_num, by simpa using ne_of_gt hr.1⟩
    have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => ((2 : ℂ) * ((r : ℝ) : ℂ))⁻¹)
        (Set.Ioo (0 : ℝ) 1) := ContDiffOn.inv hden hne
    refine ((contDiffOn_const (c := c)).mul hinv).congr ?_
    intro r hr
    simp [div_eq_mul_inv]
  have hsmooth : ∀ k : ℤ,
      ContDiffOn ℝ (⊤ : ℕ∞) (FourierCoefOfH n H k) (Set.Ioo (0 : ℝ) 1) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => starRingEnd ℂ (FourierCoefOfH n H (-k) r))
        (Set.Ioo (0 : ℝ) 1) := by
    intro k
    set MM : Fin 2 → Fin 2 → (ℝ → ℂ) := fun i j r =>
      (if j = 0 then (if i = 0 then -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ)
                      else -((p : ℂ) - 2) * ((((n : ℤ) - k : ℤ)) : ℂ))
       else (if i = 0 then -((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
             else -(p : ℂ) * ((((n : ℤ) + k : ℤ)) : ℂ))) / (2 * ((r : ℝ) : ℂ)) with hMMdef
    have hM00 : ∀ r : ℝ, MM 0 0 r
        = (-(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ)) / (2 * ((r : ℝ) : ℂ)) := by
      intro r; rw [hMMdef]; simp
    have hM01 : ∀ r : ℝ, MM 0 1 r
        = (-((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)) / (2 * ((r : ℝ) : ℂ)) := by
      intro r; rw [hMMdef]; simp
    have hM10 : ∀ r : ℝ, MM 1 0 r
        = (-((p : ℂ) - 2) * ((((n : ℤ) - k : ℤ)) : ℂ)) / (2 * ((r : ℝ) : ℂ)) := by
      intro r; rw [hMMdef]; simp
    have hM11 : ∀ r : ℝ, MM 1 1 r
        = (-(p : ℂ) * ((((n : ℤ) + k : ℤ)) : ℂ)) / (2 * ((r : ℝ) : ℂ)) := by
      intro r; rw [hMMdef]; simp
    have hM : ∀ i j : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (MM i j) (Set.Ioo (0 : ℝ) 1) := by
      intro i j
      rw [hMMdef]
      exact hMsmooth _
    have hU : ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∀ d ∈ Set.Ioo (0 : ℝ) 1,
        MeasureTheory.IntegrableOn (FourierCoefOfH n (HRad H) k) (Set.uIcc c d)
          MeasureTheory.volume := fun c hcm d hdm => (h1b k c hcm d hdm).1
    have hV : ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∀ d ∈ Set.Ioo (0 : ℝ) 1,
        MeasureTheory.IntegrableOn
          (fun s : ℝ => starRingEnd ℂ (FourierCoefOfH n (HRad H) (-k) s)) (Set.uIcc c d)
          MeasureTheory.volume :=
      fun c hcm d hdm => hconjon _ _ (h1b (-k) c hcm d hdm).1
    have hu : ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∀ d ∈ Set.Ioo (0 : ℝ) 1,
        FourierCoefOfH n H k d - FourierCoefOfH n H k c
          = ∫ s in c..d, FourierCoefOfH n (HRad H) k s :=
      fun c hcm d hdm => (h1b k c hcm d hdm).2
    have hv : ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∀ d ∈ Set.Ioo (0 : ℝ) 1,
        starRingEnd ℂ (FourierCoefOfH n H (-k) d) - starRingEnd ℂ (FourierCoefOfH n H (-k) c)
          = ∫ s in c..d, starRingEnd ℂ (FourierCoefOfH n (HRad H) (-k) s) := by
      intro c hcm d hdm
      rw [hivconj, ← (h1b (-k) c hcm d hdm).2, map_sub]
    have hsys : ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
        FourierCoefOfH n (HRad H) k r = MM 0 0 r * FourierCoefOfH n H k r
            + MM 0 1 r * starRingEnd ℂ (FourierCoefOfH n H (-k) r) ∧
          starRingEnd ℂ (FourierCoefOfH n (HRad H) (-k) r)
            = MM 1 0 r * FourierCoefOfH n H k r
              + MM 1 1 r * starRingEnd ℂ (FourierCoefOfH n H (-k) r) := by
      filter_upwards [h4 k, h4 (-k)] with r hk hmk hrmem
      have hr0 : 0 < r := hrmem.1
      have hr' : ((r : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hr0
      have hrne : (2 : ℂ) * ((r : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨by norm_num, hr'⟩
      have e1 := hk hrmem
      have e2 := hmk hrmem
      simp only [neg_neg, sub_neg_eq_add] at e2
      have e2c := congrArg (starRingEnd ℂ) e2
      simp only [map_mul, map_sub, map_neg, map_intCast, map_ofNat, Complex.conj_ofReal,
        Complex.conj_conj] at e2c
      refine ⟨?_, ?_⟩
      · rw [hM00, hM01]
        field_simp
        push_cast
        push_cast at e1
        linear_combination e1
      · rw [hM10, hM11]
        field_simp
        push_cast
        push_cast at e2c
        linear_combination e2c
    exact LinearOdeSystemSmooth 0 1 one_pos (FourierCoefOfH n H k)
      (fun r : ℝ => starRingEnd ℂ (FourierCoefOfH n H (-k) r))
      (FourierCoefOfH n (HRad H) k)
      (fun r : ℝ => starRingEnd ℂ (FourierCoefOfH n (HRad H) (-k) r))
      MM hM hU hV hu hv hsys
  -- ## Step 5: (33) at every point of `(0,1)`, from continuity
  have hagree : ∀ (f g : ℝ → ℂ), ContinuousOn f (Set.Ioo (0 : ℝ) 1) →
      ContinuousOn g (Set.Ioo (0 : ℝ) 1) →
      (∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → f r = g r) →
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, f r = g r := by
    intro f g hf hg hae r hr
    by_contra hne
    have hEopen : IsOpen {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ f x ≠ g x} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨hxmem, hxne⟩ := hx
      have hd : ContinuousAt (fun y => f y - g y) x :=
        (hf.continuousAt (isOpen_Ioo.mem_nhds hxmem)).sub
          (hg.continuousAt (isOpen_Ioo.mem_nhds hxmem))
      filter_upwards [isOpen_Ioo.mem_nhds hxmem, hd.eventually_ne (sub_ne_zero.mpr hxne)]
        with y hy1 hy2
      exact ⟨hy1, sub_ne_zero.mp hy2⟩
    have hE0 : MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ f x ≠ g x} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hcon
      exact hx.2 (hcon hx.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨r, hr, hne⟩).ne' hE0
  have h33 : ∀ (k : ℤ) (r : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 →
      2 * ((r : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) r
        = -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k r
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
              * starRingEnd ℂ (FourierCoefOfH n H (-k) r) := by
    intro k
    have hD1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (FourierCoefOfH n H k)) (Set.Ioo (0 : ℝ) 1) :=
      ((hsmooth k).1).deriv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Ioo (by simp)
    refine hagree _ _ ?_ ?_ ?_
    · exact (continuous_const.mul Complex.continuous_ofReal).continuousOn.mul hD1.continuousOn
    · exact (continuous_const.continuousOn.mul ((hsmooth k).1).continuousOn).sub
        (continuous_const.continuousOn.mul ((hsmooth k).2).continuousOn)
    · filter_upwards [h4 k, h1c k] with r h4r h1cr hrmem
      rw [(h1cr hrmem).deriv]
      exact h4r hrmem
  -- ## Steps 6 and 7: the elimination (34) and the second-order equation (35)
  refine ⟨h33, ?_, fun k => (hsmooth k).1⟩
  intro k r hr
  have hofr : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have hD1k : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (FourierCoefOfH n H k)) (Set.Ioo (0 : ℝ) 1) :=
    ((hsmooth k).1).deriv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Ioo (by simp)
  have hdak : DifferentiableAt ℝ (FourierCoefOfH n H k) r :=
    (((hsmooth k).1).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hr)
  have hdamk : DifferentiableAt ℝ (FourierCoefOfH n H (-k)) r :=
    (((hsmooth (-k)).1).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hr)
  have hdD1 : DifferentiableAt ℝ (deriv (FourierCoefOfH n H k)) r :=
    (hD1k.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hr)
  -- (E_C): the derivative of (33)
  have hEC : 2 * deriv (FourierCoefOfH n H k) r
        + 2 * ((r : ℝ) : ℂ) * deriv (deriv (FourierCoefOfH n H k)) r
      = -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * deriv (FourierCoefOfH n H k) r
        - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
            * starRingEnd ℂ (deriv (FourierCoefOfH n H (-k)) r) := by
    have heq : (fun s : ℝ => 2 * ((s : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) s)
        =ᶠ[nhds r] (fun s : ℝ => -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k s
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
              * starRingEnd ℂ (FourierCoefOfH n H (-k) s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      exact h33 k s hs
    have hL : HasDerivAt (fun s : ℝ => 2 * ((s : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) s)
        (2 * 1 * deriv (FourierCoefOfH n H k) r
          + 2 * ((r : ℝ) : ℂ) * deriv (deriv (FourierCoefOfH n H k)) r) r :=
      (hofr.const_mul 2).mul hdD1.hasDerivAt
    have hR : HasDerivAt
        (fun s : ℝ => -(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k s
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
              * starRingEnd ℂ (FourierCoefOfH n H (-k) s))
        (-(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ) * deriv (FourierCoefOfH n H k) r
          - ((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ)
              * starRingEnd ℂ (deriv (FourierCoefOfH n H (-k)) r)) r := by
      have ha := (hdak.hasDerivAt).const_mul (-(p : ℂ) * ((((n : ℤ) - k : ℤ)) : ℂ))
      have hb := ((hdamk.hasDerivAt).star).const_mul
        (((p : ℂ) - 2) * ((((n : ℤ) + k : ℤ)) : ℂ))
      exact ha.sub hb
    have hfin := hL.deriv.symm.trans (heq.deriv_eq.trans hR.deriv)
    linear_combination hfin
  -- (E_D): the elimination (34)
  have hED : 2 * ((p : ℂ) - 2) * ((r : ℝ) : ℂ)
        * starRingEnd ℂ (deriv (FourierCoefOfH n H (-k)) r)
      = 2 * (p : ℂ) * ((r : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) r
        + 4 * ((p : ℂ) - 1) * ((((n : ℤ) - k : ℤ)) : ℂ) * FourierCoefOfH n H k r := by
    have eB := h33 k r hr
    have eA0 := h33 (-k) r hr
    simp only [neg_neg, sub_neg_eq_add] at eA0
    have eA := congrArg (starRingEnd ℂ) eA0
    simp only [map_mul, map_sub, map_neg, map_intCast, map_ofNat, Complex.conj_ofReal,
      Complex.conj_conj] at eA
    push_cast at eA eB ⊢
    linear_combination ((p : ℂ) - 2) * eA - (p : ℂ) * eB
  -- (35)
  have hG : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) * deriv (FourierCoefOfH n H k) s)
      (1 * deriv (FourierCoefOfH n H k) r
        + ((r : ℝ) : ℂ) * deriv (deriv (FourierCoefOfH n H k)) r) r :=
    hofr.mul hdD1.hasDerivAt
  rw [hG.deriv]
  push_cast at hEC hED ⊢
  linear_combination (((r : ℝ) : ℂ) / 2) * hEC - (((n : ℂ) + (k : ℂ)) / 4) * hED
