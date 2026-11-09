import IwaniecManfredi.SolvesEq12
import IwaniecManfredi.PHarmonicOn
import IwaniecManfredi.WeakPartialAcrossPoint
import IwaniecManfredi.WeakPartialEqFDerivAE
import IwaniecManfredi.WirtingerChainRule
import IwaniecManfredi.WirtingerModulusPowerRule
import IwaniecManfredi.WirtingerProductRule

/-- The converse of the quoted result (C1): a solution of (12) with a
continuous potential is the complex gradient of a `p`-harmonic function.  The
paper's note demands this by name -- it lists among the facts that must be
proved "that the inverse of (54) is the complex gradient of a `p`-harmonic
function on `ℂ`" (`paper.tex:113`) -- and it is the assertion of
`paper.tex:592`.

The mechanism is the identity `div(|∇v|^{p-2} ∇v) = 2^p Re(w_z̄)` for
`w = |f|^{p-2} f` together with
`w_z̄ = |f|^{p-4}[(p/2)|f|² f_z̄ + ((p-2)/2) f² conj(f_z)]`: substituting (12)
makes the real part of the bracket vanish identically, with no case split on
`p` and no sign condition.  The potential is taken as a hypothesis in the
paper's own form `∂v/∂z = f`, because the construction of a potential is a
separate matter that uses homogeneity in Section 7 and is not part of this
step.  `S` is the zero set of `f`, locally finite; the classical identity holds
off `S`, and `WeakPartialAcrossPoint` carries both it and the weak gradient of
`v` across `S`, the growth exponent being `β = 0` since
`|f|^{p-2} f = |f|^{p-1} → 0` for `p > 1`. -/
theorem Eq12ImpliesPHarmonic (p : ℝ) (hp : 1 < p) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (S : Set ℂ) (hSΩ : S ⊆ Ω)
    (hSfin : ∀ Kc ⊆ Ω, IsCompact Kc → (S ∩ Kc).Finite)
    (f : ℂ → ℂ) (v : ℂ → ℝ)
    (hfzero : ∀ z ∈ Ω, f z = 0 ↔ z ∈ S)
    (hfcont : ContinuousOn f Ω)
    (hfsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω \ S))
    (h12 : SolvesEq12 p Ω f)
    (hvcont : ContinuousOn (fun z => ((v z : ℝ) : ℂ)) Ω)
    (hvsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((v z : ℝ) : ℂ)) (Ω \ S))
    (hvpot : ∀ z ∈ Ω \ S, DZ (fun w => ((v w : ℝ) : ℂ)) z = f z)
    (hvloc : MemLpLocOn (ENNReal.ofReal p) Ω (fun z => ((v z : ℝ) : ℂ)))
    (hfloc : MemLpLocOn (ENNReal.ofReal p) Ω f)
    (hwloc : ∀ j : Fin 2, MemLpLocOn 1 Ω
      (PartialWord [j] (fun ζ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ) * f ζ))) :
    PHarmonicOn p Ω v := by
  -- ## Step 0: `Ω - S` is open, and `S` is null
  have hΩS : IsOpen (Ω \ S) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z hz.1
    have hcl : Metric.closedBall z (ρ / 2) ⊆ Ω := fun y hy =>
      hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)))
    have hfin : (S ∩ Metric.closedBall z (ρ / 2)).Finite :=
      hSfin _ hcl (isCompact_closedBall z (ρ / 2))
    have hclosed : IsClosed (S ∩ Metric.closedBall z (ρ / 2)) := hfin.isClosed
    have hzc : z ∈ (S ∩ Metric.closedBall z (ρ / 2))ᶜ := fun h => hz.2 h.1
    filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by linarith) : z ∈ Metric.ball z (ρ / 2)),
      hclosed.isOpen_compl.mem_nhds hzc] with y hy1 hy2
    have hy1' : dist y z < ρ / 2 := Metric.mem_ball.mp hy1
    refine ⟨hball (Metric.mem_ball.mpr (by linarith)), ?_⟩
    intro hyS
    exact hy2 ⟨hyS, Metric.mem_closedBall.mpr (le_of_lt hy1')⟩
  have hSnull : MeasureTheory.volume S = 0 := by
    refine MeasureTheory.measure_null_of_locally_null S ?_
    intro z hz
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z (hSΩ hz)
    have hcl : Metric.closedBall z (ρ / 2) ⊆ Ω := fun y hy =>
      hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)))
    have hfin : (S ∩ Metric.closedBall z (ρ / 2)).Finite :=
      hSfin _ hcl (isCompact_closedBall z (ρ / 2))
    refine ⟨S ∩ Metric.ball z (ρ / 2), ?_, ?_⟩
    · exact inter_mem_nhdsWithin S
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith)))
    · exact MeasureTheory.measure_mono_null
        (Set.inter_subset_inter_right S Metric.ball_subset_closedBall)
        (hfin.measure_zero MeasureTheory.volume)
  have hSae : ∀ᵐ z : ℂ, z ∉ S := by
    have hset : ({z : ℂ | ¬ (z ∉ S)} : Set ℂ) = S := by ext z; simp
    rw [MeasureTheory.ae_iff, hset]
    exact hSnull
  -- `f` is nonzero and differentiable off `S`
  have hfne : ∀ z ∈ Ω \ S, f z ≠ 0 := fun z hz hc => hz.2 ((hfzero z hz.1).mp hc)
  have hfd : ∀ z ∈ Ω \ S, DifferentiableAt ℝ f z := fun z hz =>
    (hfsm.differentiableOn (by norm_num)).differentiableAt (hΩS.mem_nhds hz)
  -- ## Step 1: (12) at EVERY point of `Ω - S`
  have hdense : ∀ (W : Set ℂ), IsOpen W → ∀ (F G : ℂ → ℂ), ContinuousOn F W → ContinuousOn G W →
      (∀ᵐ z : ℂ, z ∈ W → F z = G z) → ∀ z ∈ W, F z = G z := by
    intro W hW F G hF hG hae z hz
    by_contra hne
    have hEopen : IsOpen {x : ℂ | x ∈ W ∧ F x ≠ G x} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨hxmem, hxne⟩ := hx
      have hd : ContinuousAt (fun y => F y - G y) x :=
        (hF.continuousAt (hW.mem_nhds hxmem)).sub (hG.continuousAt (hW.mem_nhds hxmem))
      filter_upwards [hW.mem_nhds hxmem, hd.eventually_ne (sub_ne_zero.mpr hxne)]
        with y hy1 hy2
      exact ⟨hy1, sub_ne_zero.mp hy2⟩
    have hE0 : MeasureTheory.volume {x : ℂ | x ∈ W ∧ F x ≠ G x} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hcon
      exact hx.2 (hcon hx.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨z, hz, hne⟩).ne' hE0
  obtain ⟨af, bf, hWW, h12ae⟩ := h12
  obtain ⟨fx, fy, hfL, hfxL, hfyL, hfw0, hfw1, hafdef, hbfdef⟩ := hWW
  have hfdae : ∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ f z := by
    filter_upwards [hSae] with z hz hzΩ
    exact hfd z ⟨hzΩ, hz⟩
  have hbridge := WeakPartialEqFDerivAE Ω hΩ f (fun j => if j = 0 then fx else fy) hfL
    (fun j => by
      fin_cases j
      · show MemLpLocOn 1 Ω fx
        exact hfxL
      · show MemLpLocOn 1 Ω fy
        exact hfyL)
    (fun j => by
      fin_cases j
      · show IsWeakPartialOn Ω 0 f fx
        exact hfw0
      · show IsWeakPartialOn Ω 1 f fy
        exact hfw1)
    hfdae
  have h12ptae : ∀ᵐ z : ℂ, z ∈ Ω \ S →
      DZbar f z = ((1 / p - 1 / 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)) := by
    filter_upwards [h12ae, hbridge 0, hbridge 1] with z h1 h2 h3 hz
    have e2 : fx z = fderiv ℝ f z 1 := h2 hz.1
    have e3 : fy z = fderiv ℝ f z Complex.I := h3 hz.1
    have eaf : af z = DZ f z := by rw [hafdef z, DZ, e2, e3]
    have ebf : bf z = DZbar f z := by rw [hbfdef z, DZbar, e2, e3]
    have h := h1 hz.1 (hfne z hz)
    rw [eaf, ebf] at h
    exact h
  -- continuity of both sides on `Ω - S`
  have hfdc : ContinuousOn (fderiv ℝ f) (Ω \ S) :=
    hfsm.continuousOn_fderiv_of_isOpen hΩS (by norm_num)
  have hev : ∀ u : ℂ, ContinuousOn (fun z => fderiv ℝ f z u) (Ω \ S) := fun u =>
    (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp_continuousOn hfdc
  have hDZc : ContinuousOn (fun z => DZ f z) (Ω \ S) := by
    unfold DZ
    exact continuousOn_const.mul ((hev 1).sub (continuousOn_const.mul (hev Complex.I)))
  have hDZbc : ContinuousOn (fun z => DZbar f z) (Ω \ S) := by
    unfold DZbar
    exact continuousOn_const.mul ((hev 1).add (continuousOn_const.mul (hev Complex.I)))
  have hfC : ContinuousOn f (Ω \ S) := hfcont.mono Set.sdiff_subset
  have hcjC : ContinuousOn (fun z => starRingEnd ℂ (f z)) (Ω \ S) :=
    Complex.continuous_conj.comp_continuousOn hfC
  have hcjne : ∀ z ∈ Ω \ S, starRingEnd ℂ (f z) ≠ 0 := fun z hz => by
    simpa using hfne z hz
  have hRHSc : ContinuousOn (fun z : ℂ => ((1 / p - 1 / 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ (f z) / f z) * DZ f z
        + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z))) (Ω \ S) := by
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact (hcjC.div hfC hfne).mul hDZc
    · exact (hfC.div hcjC hcjne).mul (Complex.continuous_conj.comp_continuousOn hDZc)
  have h12pt : ∀ z ∈ Ω \ S, DZbar f z = ((1 / p - 1 / 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ (f z) / f z) * DZ f z
        + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)) :=
    hdense (Ω \ S) hΩS _ _ hDZbc hRHSc h12ptae
  -- ## Step 2: `f_z̄` is real on `Ω - S`
  have hreal : ∀ z ∈ Ω \ S, starRingEnd ℂ (DZbar f z) = DZbar f z := by
    intro z hz
    rw [h12pt z hz, map_mul, Complex.conj_ofReal, map_add, map_mul, map_mul,
      map_div₀, map_div₀, Complex.conj_conj, Complex.conj_conj]
    ring
  -- ## Step 3: `w = |f|^{p-2} f` is `C^∞` on `Ω - S` and continuous on `Ω`
  obtain ⟨w, hwdef⟩ : ∃ u : ℂ → ℂ,
      u = fun ζ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ) * f ζ := ⟨_, rfl⟩
  rw [← hwdef] at hwloc
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hwnorm : ∀ ζ : ℂ, ‖w ζ‖ = ‖f ζ‖ ^ (p - 1) := by
    intro ζ
    rw [hwdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f ζ)) _)]
    rcases eq_or_ne (f ζ) 0 with h | h
    · -- the second factor vanishes, so no claim about `0 ^ (p-2)` is needed
      rw [h]
      simp [Real.zero_rpow hp1.ne']
    · have hn : (0 : ℝ) < ‖f ζ‖ := norm_pos_iff.mpr h
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hn, Real.rpow_one]
  have hwcd : ∀ z ∈ Ω \ S, ContDiffAt ℝ (1 : ℕ) w z := by
    intro z hz
    have hFc : ContDiffAt ℝ (⊤ : ℕ∞) (fun ζ : ℂ => ((‖ζ‖ ^ (p - 2) : ℝ) : ℂ)) (f z) :=
      (WirtingerModulusPowerRule (p - 2) (f z) (hfne z hz)).1
    have hfc : ContDiffAt ℝ (⊤ : ℕ∞) f z := hfsm.contDiffAt (hΩS.mem_nhds hz)
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ) * f ζ) z := (hFc.comp z hfc).mul hfc
    rw [hwdef]
    exact hcomp.of_le (by norm_num)
  have hwsm : ContDiffOn ℝ (1 : ℕ) w (Ω \ S) := fun z hz => (hwcd z hz).contDiffWithinAt
  have hwd : ∀ z ∈ Ω \ S, DifferentiableAt ℝ w z := fun z hz =>
    (hwcd z hz).differentiableAt (by norm_num)
  have hwzero : ∀ z ∈ Ω, z ∈ S → w z = 0 := by
    intro z hzΩ hzS
    rw [hwdef]
    simp only
    rw [(hfzero z hzΩ).mpr hzS]
    ring
  have hwcont : ContinuousOn w Ω := by
    intro z hzΩ
    rcases Classical.em (z ∈ S) with hzS | hzS
    · -- at a zero of `f`: `‖w‖ = ‖f‖^{p-1} → 0`, using `p - 1 > 0`
      have hfz0 : f z = 0 := (hfzero z hzΩ).mpr hzS
      have hft : Filter.Tendsto (fun ζ => ‖f ζ‖) (nhdsWithin z Ω) (nhds 0) := by
        have h := (hfcont z hzΩ).norm
        rw [ContinuousWithinAt, hfz0, norm_zero] at h
        exact h
      have hrp : Filter.Tendsto (fun t : ℝ => t ^ (p - 1)) (nhds 0) (nhds 0) := by
        have h := Real.continuousAt_rpow_const (0 : ℝ) (p - 1) (Or.inr hp1.le)
        rw [ContinuousAt, Real.zero_rpow hp1.ne'] at h
        exact h
      have hgoal : Filter.Tendsto w (nhdsWithin z Ω) (nhds 0) :=
        squeeze_zero_norm (fun ζ => le_of_eq (hwnorm ζ)) (hrp.comp hft)
      rw [ContinuousWithinAt, hwzero z hzΩ hzS]
      exact hgoal
    · exact ((hwcd z ⟨hzΩ, hzS⟩).continuousAt).continuousWithinAt
  -- ## Step 4: the formula for `w_z̄` on `Ω - S`
  have hwzbar : ∀ z ∈ Ω \ S, DZbar w z
      = ((‖f z‖ ^ (p - 2) : ℝ) : ℂ) * ((((p - 2) / 2 : ℝ) : ℂ) + 1) * DZbar f z
        + ((‖f z‖ ^ (p - 2) : ℝ) : ℂ) * (((p - 2) / 2 : ℝ) : ℂ)
            * (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z) := by
    intro z hz
    have hu : f z ≠ 0 := hfne z hz
    have hcu : starRingEnd ℂ (f z) ≠ 0 := by simpa using hu
    obtain ⟨hFc, hFz, hFzb⟩ := WirtingerModulusPowerRule (p - 2) (f z) hu
    have hFd : DifferentiableAt ℝ (fun ζ : ℂ => ((‖ζ‖ ^ (p - 2) : ℝ) : ℂ)) (f z) :=
      hFc.differentiableAt (by norm_num)
    obtain ⟨-, hchain⟩ := WirtingerChainRule (fun ζ : ℂ => ((‖ζ‖ ^ (p - 2) : ℝ) : ℂ)) f z
      (hfd z hz) hFd
    have hgd : DifferentiableAt ℝ (fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ)) z :=
      (hFd.comp z (hfd z hz))
    obtain ⟨-, hprod⟩ := WirtingerProductRule
      (fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ)) f z hgd (hfd z hz)
    have h1 : DZbar w z
        = DZbar (fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ)) z * f z
          + ((‖f z‖ ^ (p - 2) : ℝ) : ℂ) * DZbar f z := by
      rw [hwdef]; exact hprod
    rw [h1, hchain, hFz, hFzb]
    field_simp
    ring
  -- ## Step 5: `Re w_z̄ = 0` on `Ω - S`
  have hpC : ((p : ℝ) : ℂ) ≠ 0 := by
    simpa using (by linarith : p ≠ 0)
  have hcoefC : 2 * ((((p - 2) / 2 : ℝ) : ℂ) + 1) * (((1 / p - 1 / 2 : ℝ) : ℂ))
      + (((p - 2) / 2 : ℝ) : ℂ) = 0 := by
    push_cast
    field_simp
    ring
  have hRew : ∀ z ∈ Ω \ S, (DZbar w z).re = 0 := by
    intro z hz
    have hu : f z ≠ 0 := hfne z hz
    have hcu : starRingEnd ℂ (f z) ≠ 0 := by simpa using hu
    have hB := hreal z hz
    have hconjw : starRingEnd ℂ (DZbar w z)
        = ((‖f z‖ ^ (p - 2) : ℝ) : ℂ) * ((((p - 2) / 2 : ℝ) : ℂ) + 1) * DZbar f z
          + ((‖f z‖ ^ (p - 2) : ℝ) : ℂ) * (((p - 2) / 2 : ℝ) : ℂ)
              * (starRingEnd ℂ (f z) / f z) * DZ f z := by
      rw [hwzbar z hz]
      simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_ofReal,
        Complex.conj_conj, hB]
    have hsum : DZbar w z + starRingEnd ℂ (DZbar w z) = 0 := by
      -- the `conj` pattern must be rewritten BEFORE the atomic one
      rw [hconjw, hwzbar z hz, h12pt z hz]
      linear_combination (((‖f z‖ ^ (p - 2) : ℝ) : ℂ) *
        ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z))) * hcoefC
    have hac := Complex.add_conj (DZbar w z)
    rw [hsum] at hac
    have : ((2 * (DZbar w z).re : ℝ) : ℂ) = 0 := hac.symm
    have h2 : (2 * (DZbar w z).re : ℝ) = 0 := by exact_mod_cast this
    linarith
  -- ## reusable: continuity on `Ω` gives local integrability, and a local bound near `S`
  have hcontLp : ∀ u : ℂ → ℂ, ContinuousOn u Ω → MemLpLocOn 1 Ω u := by
    intro u hu K hKsub hK
    rw [MeasureTheory.memLp_one_iff_integrable,
      MeasureTheory.integrable_indicator_iff hK.measurableSet]
    exact (hu.mono hKsub).integrableOn_compact hK
  have hgrow0 : ∀ u : ℂ → ℂ, ContinuousOn u Ω → ∀ z₀ ∈ S, ∃ M ρ : ℝ, 0 < ρ ∧
      ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < ρ → ‖u z‖ ≤ M * ‖z - z₀‖ ^ (-(0 : ℝ)) := by
    intro u hu z₀ hz₀
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ (hSΩ hz₀)
    have hcl : Metric.closedBall z₀ (ρ / 2) ⊆ Ω := fun y hy =>
      hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)))
    obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ (ρ / 2)).exists_bound_of_continuousOn
      (hu.mono hcl)
    refine ⟨C, ρ / 2, by linarith, ?_⟩
    intro z _ hlt
    have hmem : z ∈ Metric.closedBall z₀ (ρ / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact hC z hmem
  -- ## Step 6: the gradient field `g = 2 conj f`
  obtain ⟨gw, hgwdef⟩ : ∃ u : ℂ → ℂ, u = fun z => 2 * starRingEnd ℂ (f z) := ⟨_, rfl⟩
  have hgwcont : ContinuousOn gw Ω := by
    rw [hgwdef]
    exact continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hfcont)
  have hgre : ∀ z : ℂ, (gw z).re = 2 * (f z).re := by
    intro z; rw [hgwdef]; simp
  have hgim : ∀ z : ℂ, (gw z).im = -(2 * (f z).im) := by
    intro z; rw [hgwdef]; simp
  -- `Re` and `Im` commute with the classical partials
  have hrecomm : ∀ (u : ℂ → ℂ) (z : ℂ), DifferentiableAt ℝ u z → ∀ j : Fin 2,
      PartialWord [j] (fun ζ => (((u ζ).re : ℝ) : ℂ)) z
        = (((PartialWord [j] u z).re : ℝ) : ℂ) := by
    intro u z hu j
    have hL : HasFDerivAt (fun ζ => (((u ζ).re : ℝ) : ℂ))
        ((Complex.ofRealCLM.comp Complex.reCLM).comp (fderiv ℝ u z)) z :=
      (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.comp z hu.hasFDerivAt
    show fderiv ℝ (fun ζ => (((u ζ).re : ℝ) : ℂ)) z (if j = 0 then (1 : ℂ) else Complex.I) = _
    rw [hL.fderiv]
    rfl
  have himcomm : ∀ (u : ℂ → ℂ) (z : ℂ), DifferentiableAt ℝ u z → ∀ j : Fin 2,
      PartialWord [j] (fun ζ => (((u ζ).im : ℝ) : ℂ)) z
        = (((PartialWord [j] u z).im : ℝ) : ℂ) := by
    intro u z hu j
    have hL : HasFDerivAt (fun ζ => (((u ζ).im : ℝ) : ℂ))
        ((Complex.ofRealCLM.comp Complex.imCLM).comp (fderiv ℝ u z)) z :=
      (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt.comp z hu.hasFDerivAt
    show fderiv ℝ (fun ζ => (((u ζ).im : ℝ) : ℂ)) z (if j = 0 then (1 : ℂ) else Complex.I) = _
    rw [hL.fderiv]
    rfl
  have hphid : ∀ z ∈ Ω \ S, DifferentiableAt ℝ (fun ζ => ((v ζ : ℝ) : ℂ)) z := fun z hz =>
    (hvsm.differentiableOn (by norm_num)).differentiableAt (hΩS.mem_nhds hz)
  -- the partials of `φ_v` are real, because `φ_v` takes real values
  have hpartim : ∀ z ∈ Ω \ S, ∀ j : Fin 2,
      (PartialWord [j] (fun ζ => ((v ζ : ℝ) : ℂ)) z).im = 0 := by
    intro z hz j
    have h := himcomm (fun ζ => ((v ζ : ℝ) : ℂ)) z (hphid z hz) j
    have hzf : (fun ζ : ℂ => (((((v ζ : ℝ) : ℂ)).im : ℝ) : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
      funext ζ; simp
    rw [hzf] at h
    have h0 : PartialWord [j] (fun _ : ℂ => (0 : ℂ)) z = 0 := by
      show fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z (if j = 0 then (1 : ℂ) else Complex.I) = 0
      simp
    rw [h0] at h
    exact_mod_cast h.symm
  -- (4): the classical partials of `φ_v` are `Re gw` and `Im gw`
  have h4 : ∀ z ∈ Ω \ S,
      PartialWord [0] (fun ζ => ((v ζ : ℝ) : ℂ)) z = (((gw z).re : ℝ) : ℂ) ∧
      PartialWord [1] (fun ζ => ((v ζ : ℝ) : ℂ)) z = (((gw z).im : ℝ) : ℂ) := by
    intro z hz
    have hdz := hvpot z hz
    have hP0im : (PartialWord [0] (fun ζ => ((v ζ : ℝ) : ℂ)) z).im = 0 := hpartim z hz 0
    have hP1im : (PartialWord [1] (fun ζ => ((v ζ : ℝ) : ℂ)) z).im = 0 := hpartim z hz 1
    have hexp : DZ (fun ζ => ((v ζ : ℝ) : ℂ)) z
        = (1 / 2 : ℂ) * (PartialWord [0] (fun ζ => ((v ζ : ℝ) : ℂ)) z
          - Complex.I * PartialWord [1] (fun ζ => ((v ζ : ℝ) : ℂ)) z) := rfl
    obtain ⟨a, hadef⟩ : ∃ t : ℝ,
        t = (PartialWord [0] (fun ζ => ((v ζ : ℝ) : ℂ)) z).re := ⟨_, rfl⟩
    obtain ⟨b, hbdef⟩ : ∃ t : ℝ,
        t = (PartialWord [1] (fun ζ => ((v ζ : ℝ) : ℂ)) z).re := ⟨_, rfl⟩
    have hP0 : PartialWord [0] (fun ζ => ((v ζ : ℝ) : ℂ)) z = ((a : ℝ) : ℂ) := by
      rw [hadef]
      exact Complex.ext rfl (by rw [Complex.ofReal_im, hP0im])
    have hP1 : PartialWord [1] (fun ζ => ((v ζ : ℝ) : ℂ)) z = ((b : ℝ) : ℂ) := by
      rw [hbdef]
      exact Complex.ext rfl (by rw [Complex.ofReal_im, hP1im])
    have hkey : ((a : ℝ) : ℂ) - Complex.I * ((b : ℝ) : ℂ) = 2 * f z := by
      rw [hexp, hP0, hP1] at hdz
      linear_combination 2 * hdz
    have hre2 : a = 2 * (f z).re := by
      have h := congrArg Complex.re hkey
      simp at h
      linarith
    have him2 : b = -(2 * (f z).im) := by
      have h := congrArg Complex.im hkey
      simp at h
      linarith
    refine ⟨?_, ?_⟩
    · rw [hP0]
      congr 1
      rw [hgre z]
      exact hre2
    · rw [hP1]
      congr 1
      rw [hgim z]
      exact him2
  -- ## Step 7: the weak gradient of `v` on all of `Ω`
  have hgrecont : ContinuousOn (fun z => (((gw z).re : ℝ) : ℂ)) Ω :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hgwcont)
  have hgimcont : ContinuousOn (fun z => (((gw z).im : ℝ) : ℂ)) Ω :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hgwcont)
  have hwp0 : IsWeakPartialOn Ω 0 (fun z => ((v z : ℝ) : ℂ)) (fun z => (((gw z).re : ℝ) : ℂ)) :=
    WeakPartialAcrossPoint Ω hΩ S hSΩ hSfin 0 _ _ 0 le_rfl one_pos
      (hvsm.of_le (by norm_num)) (fun z hz => (h4 z hz).1)
      (hcontLp _ hvcont) (hcontLp _ hgrecont) (hgrow0 _ hvcont)
  have hwp1 : IsWeakPartialOn Ω 1 (fun z => ((v z : ℝ) : ℂ)) (fun z => (((gw z).im : ℝ) : ℂ)) :=
    WeakPartialAcrossPoint Ω hΩ S hSΩ hSfin 1 _ _ 0 le_rfl one_pos
      (hvsm.of_le (by norm_num)) (fun z hz => (h4 z hz).2)
      (hcontLp _ hvcont) (hcontLp _ hgimcont) (hgrow0 _ hvcont)
  -- ## reusable: `Re` and `Im` preserve local `L¹`
  have hreLp : ∀ u : ℂ → ℂ, MemLpLocOn 1 Ω u →
      MemLpLocOn 1 Ω (fun z => (((u z).re : ℝ) : ℂ)) := by
    intro u hu K hKsub hK
    have h := hu K hKsub hK
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z => (((K.indicator u z).re : ℝ) : ℂ)) MeasureTheory.volume :=
      (Complex.continuous_ofReal.comp Complex.continuous_re).comp_aestronglyMeasurable
        h.aestronglyMeasurable
    have heq : (fun z => (((K.indicator u z).re : ℝ) : ℂ))
        =ᵐ[MeasureTheory.volume] K.indicator (fun z => (((u z).re : ℝ) : ℂ)) := by
      filter_upwards with z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    refine MeasureTheory.MemLp.mono h (h1.congr heq) ?_
    filter_upwards with z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_real,
        Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  have himLp : ∀ u : ℂ → ℂ, MemLpLocOn 1 Ω u →
      MemLpLocOn 1 Ω (fun z => (((u z).im : ℝ) : ℂ)) := by
    intro u hu K hKsub hK
    have h := hu K hKsub hK
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z => (((K.indicator u z).im : ℝ) : ℂ)) MeasureTheory.volume :=
      (Complex.continuous_ofReal.comp Complex.continuous_im).comp_aestronglyMeasurable
        h.aestronglyMeasurable
    have heq : (fun z => (((K.indicator u z).im : ℝ) : ℂ))
        =ᵐ[MeasureTheory.volume] K.indicator (fun z => (((u z).im : ℝ) : ℂ)) := by
      filter_upwards with z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    refine MeasureTheory.MemLp.mono h (h1.congr heq) ?_
    filter_upwards with z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_real,
        Real.norm_eq_abs]
      exact Complex.abs_im_le_norm _
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  -- ## Step 8, first half: the weak partials of `W₁ = Re w` and `W₂ = Im w`
  have hW1cont : ContinuousOn (fun z => (((w z).re : ℝ) : ℂ)) Ω :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hwcont)
  have hW2cont : ContinuousOn (fun z => (((w z).im : ℝ) : ℂ)) Ω :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hwcont)
  have hW1sm : ContDiffOn ℝ (1 : ℕ) (fun z => (((w z).re : ℝ) : ℂ)) (Ω \ S) :=
    (ContinuousLinearMap.contDiff
      (Complex.ofRealCLM.comp Complex.reCLM)).comp_contDiffOn hwsm
  have hW2sm : ContDiffOn ℝ (1 : ℕ) (fun z => (((w z).im : ℝ) : ℂ)) (Ω \ S) :=
    (ContinuousLinearMap.contDiff
      (Complex.ofRealCLM.comp Complex.imCLM)).comp_contDiffOn hwsm
  have hW1wp : IsWeakPartialOn Ω 0 (fun z => (((w z).re : ℝ) : ℂ))
      (fun z => (((PartialWord [0] w z).re : ℝ) : ℂ)) :=
    WeakPartialAcrossPoint Ω hΩ S hSΩ hSfin 0 _ _ 0 le_rfl one_pos hW1sm
      (fun z hz => hrecomm w z (hwd z hz) 0)
      (hcontLp _ hW1cont) (hreLp _ (hwloc 0)) (hgrow0 _ hW1cont)
  have hW2wp : IsWeakPartialOn Ω 1 (fun z => (((w z).im : ℝ) : ℂ))
      (fun z => (((PartialWord [1] w z).im : ℝ) : ℂ)) :=
    WeakPartialAcrossPoint Ω hΩ S hSΩ hSfin 1 _ _ 0 le_rfl one_pos hW2sm
      (fun z hz => himcomm w z (hwd z hz) 1)
      (hcontLp _ hW2cont) (himLp _ (hwloc 1)) (hgrow0 _ hW2cont)
  -- ## (7): the two classical partials cancel on `Ω - S`
  have h7 : ∀ z ∈ Ω \ S, (PartialWord [0] w z).re - (PartialWord [1] w z).im = 0 := by
    intro z hz
    have h := hRew z hz
    have hexp : DZbar w z
        = (1 / 2 : ℂ) * (PartialWord [0] w z + Complex.I * PartialWord [1] w z) := rfl
    rw [hexp] at h
    simp at h
    linarith
  -- ## (5): the pointwise algebra relating `|g|^{p-2} g` to `w`
  have hgwnorm : ∀ z : ℂ, ‖gw z‖ = 2 * ‖f z‖ := by
    intro z; rw [hgwdef]; simp
  have hwre : ∀ z : ℂ, (w z).re = ‖f z‖ ^ (p - 2) * (f z).re := by
    intro z; rw [hwdef]; simp
  have hwim : ∀ z : ℂ, (w z).im = ‖f z‖ ^ (p - 2) * (f z).im := by
    intro z; rw [hwdef]; simp
  have hsplit2 : ∀ z : ℂ, ‖gw z‖ ^ (p - 2) = 2 ^ (p - 2) * ‖f z‖ ^ (p - 2) := by
    intro z
    rw [hgwnorm z, Real.mul_rpow (by norm_num) (norm_nonneg (f z))]
  have h2pow : (2 : ℝ) ^ (p - 2) * 2 = 2 ^ (p - 1) := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have h5a : ∀ z : ℂ, ‖gw z‖ ^ (p - 2) * (gw z).re = 2 ^ (p - 1) * (w z).re := by
    intro z
    rw [hsplit2 z, hgre z, hwre z, ← h2pow]
    ring
  have h5b : ∀ z : ℂ, ‖gw z‖ ^ (p - 2) * (gw z).im = -(2 ^ (p - 1) * (w z).im) := by
    intro z
    rw [hsplit2 z, hgim z, hwim z, ← h2pow]
    ring
  -- ## Step 9: assemble `PHarmonicOn`
  have hgwloc : MemLpLocOn (ENNReal.ofReal p) Ω gw := by
    intro K hKsub hK
    have h := hfloc K hKsub hK
    have heq : K.indicator gw = fun z => 2 * starRingEnd ℂ (K.indicator f z) := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hgwdef]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    refine MeasureTheory.MemLp.mono (h.const_mul 2) ?_ ?_
    · rw [heq]
      exact ((continuous_const.mul Complex.continuous_conj)).comp_aestronglyMeasurable
        h.aestronglyMeasurable
    · filter_upwards with z
      rw [heq]
      simp
  refine ⟨gw, hvloc, hgwloc, hwp0, hwp1, ?_⟩
  intro φ hφ
  -- `φ` is differentiable and its complex form differentiates by `ofReal`
  have hφC : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => ((φ z : ℝ) : ℂ)) := hφ.1
  have hφR : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (((φ z : ℝ) : ℂ)).re) :=
      Complex.reCLM.contDiff.comp hφC
    have h2 : (fun z : ℂ => (((φ z : ℝ) : ℂ)).re) = φ := by funext z; simp
    rwa [h2] at h1
  have hφd : Differentiable ℝ φ := hφR.differentiable (by norm_num)
  have hfdφ : ∀ z u : ℂ, fderiv ℝ (fun y : ℂ => ((φ y : ℝ) : ℂ)) z u
      = ((fderiv ℝ φ z u : ℝ) : ℂ) := by
    intro z u
    have hL : HasFDerivAt (fun y : ℂ => ((φ y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (hφd z).hasFDerivAt
    rw [hL.fderiv]
    rfl
  -- the compact support, and vanishing of `φ` and `dφ` off it
  obtain ⟨T, hTdef⟩ : ∃ A : Set ℂ, A = tsupport (fun y : ℂ => ((φ y : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hT : IsCompact T := by rw [hTdef]; exact hφ.2.1
  have hTΩ : T ⊆ Ω := by rw [hTdef]; exact hφ.2.2
  have hφvan : ∀ z : ℂ, z ∉ T → φ z = 0 := by
    intro z hz
    rw [hTdef] at hz
    have h := image_eq_zero_of_notMem_tsupport hz
    exact_mod_cast h
  have hdvan : ∀ z : ℂ, z ∉ T → fderiv ℝ φ z = 0 := by
    intro z hz
    rw [hTdef] at hz
    have hopen : IsOpen (tsupport (fun y : ℂ => ((φ y : ℝ) : ℂ)))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev : ∀ y ∈ (tsupport (fun y : ℂ => ((φ y : ℝ) : ℂ)))ᶜ, φ y = (fun _ : ℂ => (0 : ℝ)) y := by
      intro y hy
      have h := image_eq_zero_of_notMem_tsupport hy
      exact_mod_cast h
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) hev)]
    simp
  have hdcont : ∀ u : ℂ, Continuous (fun z : ℂ => fderiv ℝ φ z u) := fun u =>
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.comp (hφR.continuous_fderiv (by norm_num))
  -- integrability of a continuous-on-`Ω` function against something supported in `T`
  have hintR : ∀ (u : ℂ → ℝ), ContinuousOn u Ω → ∀ (d : ℂ → ℝ), Continuous d →
      (∀ z : ℂ, z ∉ T → d z = 0) →
      MeasureTheory.Integrable (fun z => u z * d z) MeasureTheory.volume := by
    intro u hu d hd hdv
    have heq : (fun z => u z * d z) = T.indicator (fun z => u z * d z) := by
      funext z
      by_cases hz : z ∈ T
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hdv z hz, mul_zero]
    rw [heq, MeasureTheory.integrable_indicator_iff hT.measurableSet]
    exact ((hu.mono hTΩ).mul hd.continuousOn).integrableOn_compact hT
  have hwReCont : ContinuousOn (fun z => (w z).re) Ω :=
    Complex.continuous_re.comp_continuousOn hwcont
  have hwImCont : ContinuousOn (fun z => (w z).im) Ω :=
    Complex.continuous_im.comp_continuousOn hwcont
  have hintA : MeasureTheory.Integrable
      (fun z => (w z).re * fderiv ℝ φ z 1) MeasureTheory.volume :=
    hintR _ hwReCont _ (hdcont 1) (fun z hz => by rw [hdvan z hz]; rfl)
  have hintB : MeasureTheory.Integrable
      (fun z => (w z).im * fderiv ℝ φ z Complex.I) MeasureTheory.volume :=
    hintR _ hwImCont _ (hdcont Complex.I) (fun z hz => by rw [hdvan z hz]; rfl)
  -- transfer the two weak-partial identities from `ℂ` to `ℝ`
  have eI1 : (if (1 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = Complex.I := by norm_num
  -- `integral_ofReal` unifies only up to defeq, so state each instance as a typed `have`
  have hofR : ∀ F : ℂ → ℝ, (∫ z : ℂ, ((F z : ℝ) : ℂ)) = (((∫ z : ℂ, F z) : ℝ) : ℂ) := by
    intro F
    exact integral_ofReal (𝕜 := ℂ) (f := F) (μ := MeasureTheory.volume)
  have hA : (∫ z, (w z).re * fderiv ℝ φ z 1)
      = -∫ z, (PartialWord [0] w z).re * φ z := by
    have h := hW1wp (fun y : ℂ => ((φ y : ℝ) : ℂ)) hφ
    simp only [hfdφ, if_true] at h
    have e1 : (fun z : ℂ => (((w z).re : ℝ) : ℂ) * ((fderiv ℝ φ z 1 : ℝ) : ℂ))
        = fun z : ℂ => (((w z).re * fderiv ℝ φ z 1 : ℝ) : ℂ) := by
      funext z; push_cast; ring
    have e2 : (fun z : ℂ => (((PartialWord [0] w z).re : ℝ) : ℂ) * ((φ z : ℝ) : ℂ))
        = fun z : ℂ => (((PartialWord [0] w z).re * φ z : ℝ) : ℂ) := by
      funext z; push_cast; ring
    rw [e1, e2, hofR (fun z : ℂ => (w z).re * fderiv ℝ φ z 1),
      hofR (fun z : ℂ => (PartialWord [0] w z).re * φ z)] at h
    exact_mod_cast h
  have hB : (∫ z, (w z).im * fderiv ℝ φ z Complex.I)
      = -∫ z, (PartialWord [1] w z).im * φ z := by
    have h := hW2wp (fun y : ℂ => ((φ y : ℝ) : ℂ)) hφ
    simp only [eI1, hfdφ] at h
    have e1 : (fun z : ℂ => (((w z).im : ℝ) : ℂ) * ((fderiv ℝ φ z Complex.I : ℝ) : ℂ))
        = fun z : ℂ => (((w z).im * fderiv ℝ φ z Complex.I : ℝ) : ℂ) := by
      funext z; push_cast; ring
    have e2 : (fun z : ℂ => (((PartialWord [1] w z).im : ℝ) : ℂ) * ((φ z : ℝ) : ℂ))
        = fun z : ℂ => (((PartialWord [1] w z).im * φ z : ℝ) : ℂ) := by
      funext z; push_cast; ring
    rw [e1, e2, hofR (fun z : ℂ => (w z).im * fderiv ℝ φ z Complex.I),
      hofR (fun z : ℂ => (PartialWord [1] w z).im * φ z)] at h
    exact_mod_cast h
  -- the two right-hand sides agree, by (7) and `S` null
  have hXeq : (∫ z, (PartialWord [0] w z).re * φ z)
      = ∫ z, (PartialWord [1] w z).im * φ z := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hSae] with z hzS
    by_cases hzΩ : z ∈ Ω
    · have h := h7 z ⟨hzΩ, hzS⟩
      have : (PartialWord [0] w z).re = (PartialWord [1] w z).im := by linarith
      rw [this]
    · by_cases hzT : z ∈ T
      · exact absurd (hTΩ hzT) hzΩ
      · rw [hφvan z hzT]
        ring
  -- the pointwise form of the integrand, then the conclusion
  have hpt : ∀ z : ℂ, ‖gw z‖ ^ (p - 2) *
      (gw z * starRingEnd ℂ (((fderiv ℝ φ z 1 : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ φ z Complex.I : ℝ) : ℂ))).re
      = 2 ^ (p - 1) * ((w z).re * fderiv ℝ φ z 1
          - (w z).im * fderiv ℝ φ z Complex.I) := by
    intro z
    have hre : (gw z * starRingEnd ℂ (((fderiv ℝ φ z 1 : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ φ z Complex.I : ℝ) : ℂ))).re
        = (gw z).re * fderiv ℝ φ z 1 + (gw z).im * fderiv ℝ φ z Complex.I := by
      simp
    rw [hre]
    linear_combination (fderiv ℝ φ z 1) * h5a z
      + (fderiv ℝ φ z Complex.I) * h5b z
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hintA hintB, hA, hB, hXeq]
  ring
