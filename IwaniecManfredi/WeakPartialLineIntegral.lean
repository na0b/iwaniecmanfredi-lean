import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.IsWeakPartialOn
import IwaniecManfredi.MollificationL1Convergence
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option maxHeartbeats 1000000


open MeasureTheory

/-- A locally integrable function with a locally integrable distributional
`j`-th partial derivative is absolutely continuous along almost every line
parallel to `e_j`: on each compact `K ⊆ Ω` there is a scale `δ > 0` such that
for every increment `t` with `|t| ≤ δ`,
`u(z + t e_j) - u(z) = ∫_0^t D(z + s e_j) ds` for almost every `z ∈ K`.

This is the only route from the integration-by-parts identity of
`IsWeakPartialOn`, which sees `u` only through integrals against test
functions, to pointwise information about the increments of `u` itself.  The
paper uses it implicitly wherever Sections 4 to 6 read the `W^{1,2}`
derivatives of `H` -- and of the inverse `χ` -- as classical ones: without an
identity of this kind the distributional derivative carries no information
about the difference quotients of a representative. -/
theorem WeakPartialLineIntegral (Ω : Set ℂ) (hΩ : IsOpen Ω) (j : Fin 2) (u D : ℂ → ℂ)
    (hu : MemLpLocOn 1 Ω u) (hD : MemLpLocOn 1 Ω D)
    (hweak : IsWeakPartialOn Ω j u D)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∀ t : ℝ, |t| ≤ δ →
      ∀ᵐ z : ℂ, z ∈ K →
        u (z + t • (if j = 0 then 1 else Complex.I)) - u z
          = ∫ s in (0 : ℝ)..t, D (z + s • (if j = 0 then 1 else Complex.I)) := by
  -- ===================================================================
  -- Steps 0 to 4 of the NL proof.
  -- ===================================================================
  -- STEP 0a: the vacuous case `K = ∅`.
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun t _ => by simp [hKe]⟩
  -- STEP 0b: a scale δ with the closed 3δ-collar of K inside Ω.
  obtain ⟨δ₀, hδ₀, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨min (δ₀ / 4) 1, lt_min (by linarith) one_pos, ?_⟩
  set δ : ℝ := min (δ₀ / 4) 1 with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have h3δ : 3 * δ ≤ δ₀ := by
    have : δ ≤ δ₀ / 4 := min_le_left _ _
    linarith
  set W : Set ℂ := Metric.cthickening (3 * δ) K with hWdef
  have hWΩ : W ⊆ Ω := (Metric.cthickening_mono h3δ K).trans hδΩ
  have hWcomp : IsCompact W := hK.cthickening
  -- STEP 1: the truncations `U`, `V` are in `L¹(ℂ)`.
  set U : ℂ → ℂ := W.indicator u with hUdef
  set V : ℂ → ℂ := W.indicator D with hVdef
  have hU : Integrable U volume := by
    rw [hUdef]; exact memLp_one_iff_integrable.mp (hu W hWΩ hWcomp)
  have hV : Integrable V volume := by
    rw [hVdef]; exact memLp_one_iff_integrable.mp (hD W hWΩ hWcomp)
  -- the direction vector
  set e : ℂ := if j = 0 then 1 else Complex.I with hedef
  have hene : ‖e‖ = 1 := by rw [hedef]; split <;> simp
  -- the 2δ-collar, written with an explicit nearest point so that the
  -- triangle inequality is elementary
  set C2 : Set ℂ := {z : ℂ | ∃ y ∈ K, dist z y ≤ 2 * δ} with hC2def
  have hC2W : ∀ z ∈ C2, ∀ w : ℂ, dist w z ≤ δ → w ∈ W := by
    intro z hz w hw
    obtain ⟨y, hyK, hzy⟩ := hz
    exact Metric.mem_cthickening_of_dist_le w y (3 * δ) K hyK
      (le_trans (dist_triangle w z y) (by linarith))
  have hKC2 : ∀ z ∈ K, z ∈ C2 := fun z hz => ⟨z, hz, by simp; linarith⟩
  -- the mollifier family
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun m =>
    { rIn := δ / (m + 1) / 2
      rOut := δ / (m + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) } with hφdef
  have hrOut : ∀ m : ℕ, (φ m).rOut = δ / (m + 1) := fun m => rfl
  have hrδ : ∀ m : ℕ, (φ m).rOut ≤ δ := by
    intro m
    rw [hrOut, div_le_iff₀ (by positivity)]
    nlinarith [hδpos, Nat.cast_nonneg (α := ℝ) m]
  set Lf : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hLfdef
  -- STEP 2: transport of (H2).  For `z` in the collar the `e`-component of the
  -- derivative of the mollification of `U` is the mollification of `V`.
  have step2 : ∀ m : ℕ, ∀ z ∈ C2,
      (convolution U (fderiv ℝ ((φ m).normed volume)) (Lf.precompR ℂ) volume z) e
        = convolution V ((φ m).normed volume) Lf volume z := by
    intro m z hz
    set ρ : ℂ → ℝ := (φ m).normed volume with hρdef
    have hρsmooth : ContDiff ℝ (⊤ : ℕ∞) ρ := (φ m).contDiff_normed
    have hρtsupp : tsupport ρ = Metric.closedBall (0 : ℂ) (φ m).rOut :=
      (φ m).tsupport_normed_eq
    -- (2d) the indicator-matching helper
    have hmatch : ∀ w : ℂ, dist w z ≤ (φ m).rOut → w ∈ W := fun w hw =>
      hC2W z hz w (le_trans hw (hrδ m))
    have hballdist : ∀ w : ℂ, z - w ∈ Metric.closedBall (0 : ℂ) (φ m).rOut →
        dist w z ≤ (φ m).rOut := by
      intro w hw
      simp only [Metric.mem_closedBall, dist_zero_right] at hw
      rw [dist_eq_norm, ← norm_neg]
      simpa using hw
    -- (2a) the test function
    set ψ : ℂ → ℂ := fun w => ((ρ (z - w) : ℝ) : ℂ) with hψdef
    have hψsupp : Function.support ψ ⊆ Metric.closedBall z (φ m).rOut := by
      intro w hw
      have hne : ρ (z - w) ≠ 0 := by
        simpa [hψdef, Complex.ofReal_eq_zero] using hw
      have hmem : z - w ∈ tsupport ρ := subset_tsupport ρ hne
      rw [hρtsupp] at hmem
      simpa [Metric.mem_closedBall] using hballdist w hmem
    have hψtsupp : tsupport ψ ⊆ Metric.closedBall z (φ m).rOut :=
      closure_minimal hψsupp Metric.isClosed_closedBall
    have hψtest : IsTestFn Ω ψ := by
      refine ⟨?_, ?_, ?_⟩
      · exact Complex.ofRealCLM.contDiff.comp
          (hρsmooth.comp (contDiff_const.sub contDiff_id))
      · exact HasCompactSupport.intro (isCompact_closedBall z (φ m).rOut)
          (fun x hx => Function.notMem_support.mp (fun hc => hx (hψsupp hc)))
      · intro w hw
        exact hWΩ (hmatch w (by simpa [Metric.mem_closedBall] using hψtsupp hw))
    -- (2b) the derivative of the test function
    have hψd : ∀ w : ℂ, fderiv ℝ ψ w e = -((fderiv ℝ ρ (z - w) e : ℝ) : ℂ) := by
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
    have hw := hweak ψ hψtest
    rw [← hedef] at hw
    simp_rw [hψd, hψdef, mul_neg] at hw
    rw [integral_neg, neg_inj] at hw
    -- hw : ∫ w, u w * ((fderiv ℝ ρ (z - w)) e : ℂ) = ∫ w, D w * ((ρ (z - w) : ℝ) : ℂ)
    -- (2d) replace `u`, `D` by their truncations, pointwise
    have hUmatch : ∀ w : ℂ, u w * (((fderiv ℝ ρ (z - w)) e : ℝ) : ℂ)
        = ((fderiv ℝ ρ (z - w)) e) • U w := by
      intro w
      by_cases hc : (fderiv ℝ ρ (z - w)) e = 0
      · simp [hc]
      · have hne : fderiv ℝ ρ (z - w) ≠ 0 := by
          intro h0; rw [h0] at hc; simp at hc
        have hmem : z - w ∈ tsupport ρ :=
          (support_fderiv_subset ℝ) (Function.mem_support.mpr hne)
        rw [hρtsupp] at hmem
        have : U w = u w := by
          rw [hUdef, Set.indicator_of_mem (hmatch w (hballdist w hmem))]
        rw [this, Complex.real_smul, mul_comm]
    have hVmatch : ∀ w : ℂ, D w * ((ρ (z - w) : ℝ) : ℂ) = (ρ (z - w)) • V w := by
      intro w
      by_cases hc : ρ (z - w) = 0
      · simp [hc]
      · have hmem : z - w ∈ tsupport ρ := subset_tsupport ρ hc
        rw [hρtsupp] at hmem
        have : V w = D w := by
          rw [hVdef, Set.indicator_of_mem (hmatch w (hballdist w hmem))]
        rw [this, Complex.real_smul, mul_comm]
    simp_rw [hUmatch, hVmatch] at hw
    -- (2e) read both sides as convolutions
    have hUloc : LocallyIntegrable U volume := hU.locallyIntegrable
    have hVloc : LocallyIntegrable V volume := hV.locallyIntegrable
    rw [convolution_precompR_apply Lf hUloc
      ((φ m).hasCompactSupport_normed.fderiv ℝ)
      (hρsmooth.continuous_fderiv (by norm_num)) z e]
    simp only [convolution_def, hLfdef, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply]
    exact hw
  -- STEP 3: the finite-difference identity for the mollification
  have step3 : ∀ m : ℕ, ∀ t : ℝ, |t| ≤ δ → ∀ z ∈ K,
      convolution U ((φ m).normed volume) Lf volume (z + t • e)
          - convolution U ((φ m).normed volume) Lf volume z
        = ∫ s in (0 : ℝ)..t, convolution V ((φ m).normed volume) Lf volume (z + s • e) := by
    intro m t ht z hz
    have hline : ∀ s : ℝ, |s| ≤ δ → z + s • e ∈ C2 := by
      intro s hs
      refine ⟨z, hz, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hene, Real.norm_eq_abs, mul_one]
      linarith
    have hFD : ∀ x : ℂ, HasFDerivAt (convolution U ((φ m).normed volume) Lf volume)
        (convolution U (fderiv ℝ ((φ m).normed volume)) (Lf.precompR ℂ) volume x) x := by
      intro x
      exact HasCompactSupport.hasFDerivAt_convolution_right
        (L := Lf) (hcg := (φ m).hasCompactSupport_normed) (hf := hU.locallyIntegrable)
        (hg := (φ m).contDiff_normed) x
    have hderiv : ∀ s : ℝ, |s| ≤ δ →
        HasDerivAt (fun σ : ℝ => convolution U ((φ m).normed volume) Lf volume (z + σ • e))
          (convolution V ((φ m).normed volume) Lf volume (z + s • e)) s := by
      intro s hs
      have hL : HasDerivAt (fun σ : ℝ => z + σ • e) e s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_add z
      have hc := HasFDerivAt.comp_hasDerivAt_of_eq
        (l := convolution U ((φ m).normed volume) Lf volume)
        (f := fun σ : ℝ => z + σ • e)
        (hl := hFD (z + s • e)) (hf := hL) (hy := rfl)
      rw [step2 m (z + s • e) (hline s hs)] at hc
      simpa [Function.comp_def] using hc
    have hVcont : Continuous (convolution V ((φ m).normed volume) Lf volume) := by
      have h : ContDiff ℝ 1 (convolution V ((φ m).normed volume) Lf volume) :=
        HasCompactSupport.contDiff_convolution_right (L := Lf)
          (hcg := (φ m).hasCompactSupport_normed) (hf := hV.locallyIntegrable)
          (hg := (φ m).contDiff_normed)
      exact h.continuous
    have hcont : Continuous
        (fun σ : ℝ => convolution V ((φ m).normed volume) Lf volume (z + σ • e)) :=
      hVcont.comp (by fun_prop)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun σ : ℝ => convolution U ((φ m).normed volume) Lf volume (z + σ • e))
      (f' := fun s : ℝ => convolution V ((φ m).normed volume) Lf volume (z + s • e))
      (a := (0 : ℝ)) (b := t)
      (fun s hs => hderiv s (by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [abs_le] at ht ⊢ <;> constructor <;> linarith [ht.1, ht.2]))
      (hcont.intervalIntegrable 0 t)
    rw [hftc]
    simp
  -- bump-family facts needed by the brick
  have hr1 : ∀ m : ℕ, (φ m).rOut ≤ 1 := fun m => le_trans (hrδ m) hδ1
  have hr0 : Filter.Tendsto (fun m : ℕ => (φ m).rOut) Filter.atTop (nhds 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
    simp only [mul_zero] at h
    refine h.congr (fun m => ?_)
    rw [hrOut]
    ring
  intro t ht
  set I : Set ℝ := Set.uIoc 0 t with hIdef
  -- the segment from z stays in W
  have hseg : ∀ z ∈ K, ∀ s : ℝ, |s| ≤ δ → z + s • e ∈ W := by
    intro z hz s hs
    refine Metric.mem_cthickening_of_dist_le _ z (3 * δ) K hz ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hene, Real.norm_eq_abs, mul_one]
    linarith
  -- the mollified families
  set um : ℕ → ℂ → ℂ := fun m => convolution U ((φ m).normed volume) Lf volume with humdef
  set vm : ℕ → ℂ → ℂ := fun m => convolution V ((φ m).normed volume) Lf volume with hvmdef
  have humint : ∀ m, Integrable (um m) volume := fun m =>
    hU.integrable_convolution Lf (φ m).integrable_normed
  have hvmint : ∀ m, Integrable (vm m) volume := fun m =>
    hV.integrable_convolution Lf (φ m).integrable_normed
  -- the brick, transported through `convolution_flip`
  have hbU : Filter.Tendsto (fun m => ∫ x, ‖um m x - U x‖) Filter.atTop (nhds 0) := by
    have h := MollificationL1Convergence U hU φ hr1 hr0
    simp_rw [humdef, hLfdef, convolution_flip]
    exact h
  have hbV : Filter.Tendsto (fun m => ∫ x, ‖vm m x - V x‖) Filter.atTop (nhds 0) := by
    have h := MollificationL1Convergence V hV φ hr1 hr0
    simp_rw [hvmdef, hLfdef, convolution_flip]
    exact h
  -- the shear `(s, z) ↦ (s, z + s • e)` preserves `volume ×ˢ volume` on `ℝ × ℂ`
  have hshear : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 + p.1 • e))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product (by fun_prop)
      (Filter.Eventually.of_forall fun s => map_add_right_eq_self volume (s • e))
  -- the Tonelli bound
  have hton : ∀ G : ℂ → ℂ, AEStronglyMeasurable G volume →
      (∫⁻ z, ∫⁻ s in I, ‖G (z + s • e)‖ₑ) ≤ (∫⁻ x, ‖G x‖ₑ) * volume I := by
    intro G hG
    have h1 : AEMeasurable (fun q : ℝ × ℂ => ‖G q.2‖ₑ) (volume.prod volume) :=
      hG.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEMeasurable (fun q : ℝ × ℂ => ‖G (q.2 + q.1 • e)‖ₑ)
        (volume.prod volume) := h1.comp_quasiMeasurePreserving hshear.quasiMeasurePreserving
    have h3 : AEMeasurable (fun p : ℂ × ℝ => ‖G (p.1 + p.2 • e)‖ₑ)
        (volume.prod (volume.restrict I)) := by
      have hsw : MeasurePreserving (Prod.swap : ℂ × ℝ → ℝ × ℂ)
          (volume.prod (volume.restrict I)) ((volume.restrict I).prod volume) :=
        Measure.measurePreserving_swap
      have h2' : AEMeasurable (fun q : ℝ × ℂ => ‖G (q.2 + q.1 • e)‖ₑ)
          ((volume.restrict I).prod volume) := by
        have : (volume.restrict I).prod (volume : Measure ℂ)
            = (volume.prod volume).restrict (I ×ˢ (Set.univ : Set ℂ)) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
        rw [this]
        exact h2.restrict
      exact h2'.comp_quasiMeasurePreserving hsw.quasiMeasurePreserving
    rw [lintegral_lintegral_swap h3]
    calc (∫⁻ s in I, ∫⁻ z, ‖G (z + s • e)‖ₑ)
        = ∫⁻ _ in I, ∫⁻ x, ‖G x‖ₑ := by
          refine setLIntegral_congr_fun measurableSet_uIoc (fun s _ => ?_)
          exact lintegral_add_right_eq_self (fun x => ‖G x‖ₑ) (s • e)
      _ = (∫⁻ x, ‖G x‖ₑ) * volume I := setLIntegral_const _ _
      _ ≤ (∫⁻ x, ‖G x‖ₑ) * volume I := le_rfl
  -- product-measurability of a translate along the segment
  have hAEprod : ∀ G : ℂ → ℂ, AEMeasurable G volume →
      AEMeasurable (fun p : ℂ × ℝ => G (p.1 + p.2 • e)) (volume.prod (volume.restrict I)) := by
    intro G hG
    have h1 : AEMeasurable (fun q : ℝ × ℂ => G q.2) (volume.prod volume) :=
      hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEMeasurable (fun q : ℝ × ℂ => G (q.2 + q.1 • e)) (volume.prod volume) :=
      h1.comp_quasiMeasurePreserving hshear.quasiMeasurePreserving
    have h2' : AEMeasurable (fun q : ℝ × ℂ => G (q.2 + q.1 • e))
        ((volume.restrict I).prod volume) := by
      have hr : (volume.restrict I).prod (volume : Measure ℂ)
          = (volume.prod volume).restrict (I ×ˢ (Set.univ : Set ℂ)) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hr]; exact h2.restrict
    exact h2'.comp_quasiMeasurePreserving
      (Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
        (ν := (volume : Measure ℝ).restrict I)).quasiMeasurePreserving
  -- Sound-gap 3: for a.e. `z` the segment integrand is integrable
  have hVprodI : Integrable (fun p : ℂ × ℝ => V (p.1 + p.2 • e))
      (volume.prod (volume.restrict I)) := by
    refine ⟨aestronglyMeasurable_iff_aemeasurable.mpr (hAEprod V hV.aemeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hsw : (∫⁻ p : ℂ × ℝ, ‖V (p.1 + p.2 • e)‖ₑ ∂(volume.prod (volume.restrict I)))
        = ∫⁻ z, ∫⁻ s in I, ‖V (z + s • e)‖ₑ :=
      lintegral_prod _ (hAEprod V hV.aemeasurable).enorm
    rw [hsw]
    refine lt_of_le_of_lt (hton V hV.aestronglyMeasurable) (ENNReal.mul_lt_top ?_ ?_)
    · rw [← hasFiniteIntegral_iff_enorm]; exact hV.2
    · have hvI : volume I = ENNReal.ofReal (0 ⊔ t - 0 ⊓ t) := by
        rw [hIdef, Set.uIoc, Real.volume_Ioc]
      rw [hvI]
      exact ENNReal.ofReal_lt_top
  have hVseg : ∀ᵐ z : ℂ, Integrable (fun s : ℝ => V (z + s • e)) (volume.restrict I) :=
    hVprodI.prod_right_ae
  have hvolI : volume I = ENNReal.ofReal |t| := by
    rw [hIdef, Set.uIoc, Real.volume_Ioc]
    congr 1
    by_cases h : (0 : ℝ) ≤ t
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg h]; ring
    · replace h : t < 0 := not_le.mp h
      rw [max_eq_left h.le, min_eq_right h.le, abs_of_neg h]; ring
  -- the three-term bound, for every `m`
  have hbound : ∀ m : ℕ, (∫⁻ z in K, ‖(U (z + t • e) - U z)
        - ∫ s in (0 : ℝ)..t, V (z + s • e)‖ₑ)
      ≤ ENNReal.ofReal (2 * (∫ x, ‖U x - um m x‖) + |t| * ∫ x, ‖vm m x - V x‖) := by
    intro m
    have hsubU : Integrable (fun x => U x - um m x) volume := hU.sub (humint m)
    have hsubV : Integrable (fun x => vm m x - V x) volume := (hvmint m).sub hV
    have hfm : AEMeasurable (fun x : ℂ => ‖U x - um m x‖ₑ) volume :=
      hsubU.aestronglyMeasurable.enorm
    have hgm : AEMeasurable
        (fun z : ℂ => ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ) volume :=
      (hAEprod (fun x => vm m x - V x) hsubV.aemeasurable).enorm.lintegral_prod_right'
    have hvcont : Continuous (vm m) := by
      have h : ContDiff ℝ 1 (vm m) := by
        rw [hvmdef]
        exact HasCompactSupport.contDiff_convolution_right (L := Lf)
          (hcg := (φ m).hasCompactSupport_normed) (hf := hV.locallyIntegrable)
          (hg := (φ m).contDiff_normed)
      exact h.continuous
    have hstep : ∀ᵐ z : ℂ ∂(volume.restrict K),
        ‖(U (z + t • e) - U z) - ∫ s in (0 : ℝ)..t, V (z + s • e)‖ₑ
          ≤ (‖U (z + t • e) - um m (z + t • e)‖ₑ + ‖U z - um m z‖ₑ)
            + ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ := by
      rw [ae_restrict_iff' hK.measurableSet]
      filter_upwards [hVseg] with z hVz hzK
      have hVint : IntervalIntegrable (fun s : ℝ => V (z + s • e)) volume 0 t := by
        rw [intervalIntegrable_iff]; exact hVz
      have hvc : Continuous (fun σ : ℝ => vm m (z + σ • e)) := hvcont.comp (by fun_prop)
      have hsplit : (∫ s in (0 : ℝ)..t, vm m (z + s • e))
          - ∫ s in (0 : ℝ)..t, V (z + s • e)
          = ∫ s in (0 : ℝ)..t, (vm m (z + s • e) - V (z + s • e)) :=
        (intervalIntegral.integral_sub (hvc.intervalIntegrable 0 t) hVint).symm
      have halg : (U (z + t • e) - U z) - ∫ s in (0 : ℝ)..t, V (z + s • e)
          = ((U (z + t • e) - um m (z + t • e)) - (U z - um m z))
            + ((∫ s in (0 : ℝ)..t, vm m (z + s • e))
              - ∫ s in (0 : ℝ)..t, V (z + s • e)) := by
        rw [← step3 m t ht z hzK]; ring
      rw [halg, hsplit]
      refine le_trans (enorm_add_le _ _) (add_le_add enorm_sub_le ?_)
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, enorm_smul]
      have hone : ‖(if (0 : ℝ) ≤ t then (1 : ℝ) else -1)‖ₑ = 1 := by split <;> simp
      rw [hone, one_mul]
      exact enorm_integral_le_lintegral_enorm _
    have hna : (0 : ℝ) ≤ ∫ x, ‖U x - um m x‖ := integral_nonneg fun _ => norm_nonneg _
    have hnb : (0 : ℝ) ≤ ∫ x, ‖vm m x - V x‖ := integral_nonneg fun _ => norm_nonneg _
    calc (∫⁻ z in K, ‖(U (z + t • e) - U z) - ∫ s in (0 : ℝ)..t, V (z + s • e)‖ₑ)
        ≤ ∫⁻ z in K, ((‖U (z + t • e) - um m (z + t • e)‖ₑ + ‖U z - um m z‖ₑ)
            + ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ) := lintegral_mono_ae hstep
      _ ≤ ∫⁻ z, ((‖U (z + t • e) - um m (z + t • e)‖ₑ + ‖U z - um m z‖ₑ)
            + ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ) :=
          setLIntegral_le_lintegral _ _
      _ = (∫⁻ z, (‖U (z + t • e) - um m (z + t • e)‖ₑ + ‖U z - um m z‖ₑ))
            + ∫⁻ z, ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ :=
          lintegral_add_right' _ hgm
      _ = ((∫⁻ z, ‖U (z + t • e) - um m (z + t • e)‖ₑ) + ∫⁻ z, ‖U z - um m z‖ₑ)
            + ∫⁻ z, ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ := by
          rw [lintegral_add_right' _ hfm]
      _ = ((∫⁻ x, ‖U x - um m x‖ₑ) + ∫⁻ x, ‖U x - um m x‖ₑ)
            + ∫⁻ z, ∫⁻ s in I, ‖vm m (z + s • e) - V (z + s • e)‖ₑ := by
          rw [lintegral_add_right_eq_self (fun x : ℂ => ‖U x - um m x‖ₑ) (t • e)]
      _ ≤ ((∫⁻ x, ‖U x - um m x‖ₑ) + ∫⁻ x, ‖U x - um m x‖ₑ)
            + (∫⁻ x, ‖vm m x - V x‖ₑ) * volume I :=
          add_le_add le_rfl (hton (fun x => vm m x - V x) hsubV.aestronglyMeasurable)
      _ = ENNReal.ofReal (2 * (∫ x, ‖U x - um m x‖) + |t| * ∫ x, ‖vm m x - V x‖) := by
          rw [← ofReal_integral_norm_eq_lintegral_enorm hsubU,
            ← ofReal_integral_norm_eq_lintegral_enorm hsubV, hvolI,
            ← ENNReal.ofReal_mul hnb, ← ENNReal.ofReal_add hna hna,
            ← ENNReal.ofReal_add (by linarith) (mul_nonneg hnb (abs_nonneg t))]
          congr 1
          ring
  -- the bound tends to `0`, so the integral vanishes
  have hlim : Filter.Tendsto
      (fun m => 2 * (∫ x, ‖U x - um m x‖) + |t| * ∫ x, ‖vm m x - V x‖)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m => ∫ x, ‖U x - um m x‖) Filter.atTop (nhds 0) := by
      refine hbU.congr fun m => ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => norm_sub_rev _ _)
    simpa using (h1.const_mul 2).add (hbV.const_mul |t|)
  have hzero : (∫⁻ z in K, ‖(U (z + t • e) - U z)
      - ∫ s in (0 : ℝ)..t, V (z + s • e)‖ₑ) = 0 := by
    refine le_antisymm ?_ (by simp)
    have hcont : Filter.Tendsto
        (fun m => ENNReal.ofReal (2 * (∫ x, ‖U x - um m x‖) + |t| * ∫ x, ‖vm m x - V x‖))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlim
    exact ge_of_tendsto' hcont hbound
  -- measurability of the integrand, so that the vanishing integral gives `= 0` a.e.
  have hBmeas : AEStronglyMeasurable
      (fun z : ℂ => ∫ s in (0 : ℝ)..t, V (z + s • e)) volume := by
    have h0 : AEStronglyMeasurable (fun z : ℂ => ∫ s in I, V (z + s • e)) volume :=
      (aestronglyMeasurable_iff_aemeasurable.mpr
        (hAEprod V hV.aemeasurable)).integral_prod_right'
    have heq : (fun z : ℂ => ∫ s in (0 : ℝ)..t, V (z + s • e))
        = fun z : ℂ => (if (0 : ℝ) ≤ t then (1 : ℝ) else -1) • ∫ s in I, V (z + s • e) := by
      funext z
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    rw [heq]
    exact h0.const_smul (if (0 : ℝ) ≤ t then (1 : ℝ) else -1)
  have hmeasAB : AEMeasurable (fun z : ℂ => ‖(U (z + t • e) - U z)
      - ∫ s in (0 : ℝ)..t, V (z + s • e)‖ₑ) volume := by
    have h1 : AEMeasurable (fun z : ℂ => U (z + t • e)) volume :=
      hU.aemeasurable.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (t • e)).quasiMeasurePreserving
    exact ((h1.sub hU.aemeasurable).sub hBmeas.aemeasurable).enorm
  rw [lintegral_eq_zero_iff' hmeasAB.restrict] at hzero
  rw [Filter.EventuallyEq, ae_restrict_iff' hK.measurableSet] at hzero
  -- `K` sits inside its own collar
  have hKW : K ⊆ W := Metric.self_subset_cthickening K
  filter_upwards [hzero] with z hz hzK
  have hUV : (U (z + t • e) - U z) - ∫ s in (0 : ℝ)..t, V (z + s • e) = 0 := by
    have := hz hzK
    simpa using this
  have h1 : U (z + t • e) = u (z + t • e) := by
    rw [hUdef, Set.indicator_of_mem (hseg z hzK t ht)]
  have h2 : U z = u z := by
    rw [hUdef, Set.indicator_of_mem (hKW hzK)]
  have h3 : (∫ s in (0 : ℝ)..t, V (z + s • e)) = ∫ s in (0 : ℝ)..t, D (z + s • e) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsδ : |s| ≤ δ := by
      have hab := Set.mem_uIcc.mp hs
      rw [abs_le] at ht
      rw [abs_le]
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨by linarith [ht.1, hδpos], by linarith [ht.2]⟩
      · exact ⟨by linarith [ht.1], by linarith [ht.2, hδpos]⟩
    rw [hVdef, Set.indicator_of_mem (hseg z hzK s hsδ)]
  rw [← h1, ← h2, ← h3]
  linear_combination hUV
