import IwaniecManfredi.Preamble
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory

/-- Mollification converges in the `L¹` norm: if `g : ℂ → ℂ` is Lebesgue
integrable and `φ n` is a sequence of smooth bump functions with outer radii
bounded by `1` and tending to `0`, then
`∫ ‖g ⋆ (φ n).normed - g‖ → 0`.

Mathlib carries the pointwise and the almost-everywhere forms of this
statement (`ContDiffBump.convolution_tendsto_right_of_continuous` and its
relatives) but not the `L¹`-norm form, which is what is needed whenever a
limit is taken inside a further integration: there the a.e. convergence of
the mollifications would require an `ε`-uniform dominating function, which
local integrability does not supply.

The proof is the standard three-epsilon argument: Young's inequality at
`p = 1` makes convolution with a probability density an `L¹` contraction,
the compactly supported continuous functions are dense in `L¹`, and for such
a function the mollifications converge in `L¹` by dominated convergence
against the indicator of one fixed closed ball. -/
theorem MollificationL1Convergence (g : ℂ → ℂ) (hg : Integrable g volume)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hr1 : ∀ n, (φ n).rOut ≤ 1)
    (hr0 : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ x, ‖convolution ((φ n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖)
      Filter.atTop (nhds 0) := by
  -- (a) The `L¹` contraction, i.e. Young's inequality at `p = 1`.
  have conv_l1 : ∀ (ρ : ℂ → ℝ) (g : ℂ → ℂ), Integrable ρ volume → Integrable g volume →
      ∫ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ ≤ (∫ t, ‖ρ t‖) * (∫ x, ‖g x‖) := by
    intro ρ g hρ hg
    have hint : Integrable
        (fun p : ℂ × ℂ => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ p.2) (g (p.1 - p.2)))
        (volume.prod volume) := hρ.convolution_integrand _ hg
    have hconv : Integrable (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
      hρ.integrable_convolution _ hg
    have hstep1 : ∫ x, ‖(convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
        ≤ ∫ x, ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖ := by
      refine integral_mono hconv.norm (hint.norm.integral_prod_left) ?_
      intro x
      exact norm_integral_le_integral_norm _
    have hswap : ∫ x, ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖
        = ∫ t, ∫ x, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖ :=
      integral_integral_swap hint.norm
    have hinner : ∀ t : ℂ, ∫ x, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖
        = ‖ρ t‖ * ∫ x, ‖g x‖ := by
      intro t
      simp only [ContinuousLinearMap.lsmul_apply, norm_smul]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun x => ‖g x‖) t
    calc ∫ x, ‖(convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
        ≤ ∫ x, ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖ := hstep1
      _ = ∫ t, ∫ x, ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (ρ t) (g (x - t))‖ := hswap
      _ = ∫ t, ‖ρ t‖ * ∫ x, ‖g x‖ := by simp_rw [hinner]
      _ = (∫ t, ‖ρ t‖) * (∫ x, ‖g x‖) := integral_mul_const _ _
  -- (b) Mollification of a compactly supported continuous function
  -- converges in `L¹`, by dominated convergence against the indicator of a
  -- fixed closed ball containing every support involved.
  have conv_cont_l1 : ∀ h : ℂ → ℂ, Continuous h → HasCompactSupport h →
      ∀ φ : ℕ → ContDiffBump (0 : ℂ), (∀ n, (φ n).rOut ≤ 1) →
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ∫ x, ‖convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖)
        Filter.atTop (nhds 0) := by
    intro h hcont hsupp φ hr1 hr0
    obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
    obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : ℂ)
    have hhint : Integrable h volume := hcont.integrable_of_hasCompactSupport hsupp
    set S : Set ℂ := Metric.closedBall (0 : ℂ) (1 + R) with hS
    have hSmeas : MeasurableSet S := measurableSet_closedBall
    have hSfin : volume S < ⊤ := Metric.isBounded_closedBall.measure_lt_top
    have hhzero : ∀ x ∉ S, h x = 0 := by
      intro x hx
      by_contra hne
      exact hx (Metric.closedBall_subset_closedBall (by linarith : R ≤ 1 + R)
        (hR (subset_tsupport h hne)))
    have hconvzero : ∀ n, ∀ x ∉ S,
        (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0 := by
      intro n x hx
      by_contra hne
      have hmem := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hne
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hmem
      rw [ContDiffBump.support_normed_eq] at ha
      have hbR : b ∈ Metric.closedBall (0 : ℂ) R := hR (subset_tsupport h hb)
      refine hx ?_
      rw [hS, Metric.mem_closedBall, dist_zero_right, ← hab]
      calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
        _ ≤ 1 + R := by
          have h1 : ‖a‖ < (φ n).rOut := by
            simpa [Metric.mem_ball, dist_zero_right] using ha
          have h2 : ‖b‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hbR
          have := hr1 n
          linarith
    -- the uniform pointwise bound, from `dist_normed_convolution_le` with `ε = 2C + 1`
    have hdist : ∀ n, ∀ x, ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖
        ≤ 2 * C + 1 := by
      intro n x
      have hb : ∀ y ∈ Metric.ball x (φ n).rOut, dist (h y) (h x) ≤ 2 * C + 1 := by
        intro y _
        calc dist (h y) (h x) ≤ ‖h y‖ + ‖h x‖ := dist_le_norm_add_norm _ _
          _ ≤ 2 * C + 1 := by have h1 := hC y; have h2 := hC x; linarith
      have hres := ContDiffBump.dist_normed_convolution_le (φ := φ n) (μ := volume)
        hcont.aestronglyMeasurable hb
      simpa [dist_eq_norm] using hres
    have hmeas : ∀ n, AEStronglyMeasurable
        (fun x => ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖) volume := fun n =>
      ((((φ n).integrable_normed).integrable_convolution _ hhint).sub hhint).aestronglyMeasurable.norm
    have hbint : Integrable (S.indicator (fun _ : ℂ => 2 * C + 1)) volume := by
      rw [integrable_indicator_iff hSmeas]
      exact integrableOn_const hSfin.ne (by simp)
    have hdom : ∀ n, ∀ᵐ x : ℂ,
        ‖‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖‖
          ≤ S.indicator (fun _ : ℂ => 2 * C + 1) x := by
      intro n
      filter_upwards with x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdist n x
      · rw [Set.indicator_of_notMem hx, hconvzero n x hx, hhzero x hx]
        simp
    have hlim : ∀ᵐ x : ℂ, Filter.Tendsto
        (fun n => ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖)
        Filter.atTop (nhds 0) := by
      filter_upwards with x
      have hcv := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hr0 hcont x
      simpa using (hcv.sub (tendsto_const_nhds (x := h x) (f := Filter.atTop))).norm
    simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
      (S.indicator (fun _ : ℂ => 2 * C + 1)) hmeas hbint hdom hlim
  -- (c) The three-epsilon argument, by density of the compactly supported
  -- continuous functions in `L¹`.
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  obtain ⟨h, hhsupp, hhle, hhcont, hhint⟩ :=
    hg.exists_hasCompactSupport_integral_sub_le (show (0 : ℝ) < η / 3 by linarith)
  have hkey : ∀ n, ∫ x, ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - g x‖
      ≤ η / 3 + (∫ x, ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖) + η / 3 := by
    intro n
    have hρint : Integrable ((φ n).normed volume) volume := (φ n).integrable_normed
    have hρnorm : ∫ t, ‖(φ n).normed volume t‖ = 1 := by
      have hpt : ∀ t, ‖(φ n).normed volume t‖ = (φ n).normed volume t := fun t =>
        Real.norm_of_nonneg ((φ n).nonneg_normed t)
      simp_rw [hpt]
      exact (φ n).integral_normed
    have hcg : Integrable (convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
      hρint.integrable_convolution _ hg
    have hch : Integrable (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
      hρint.integrable_convolution _ hhint
    -- a.e. linearity of the convolution in its right argument
    have haeg := (hρint.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg).prod_right_ae
    have haeh := (hρint.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hhint).prod_right_ae
    have hlin : ∀ᵐ x : ℂ,
        ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
            - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
          = ‖(convolution ((φ n).normed volume) (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ := by
      filter_upwards [haeg, haeh] with x hxg hxh
      simp only [ContinuousLinearMap.lsmul_apply] at hxg hxh
      congr 1
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Pi.sub_apply, smul_sub]
      exact (integral_sub hxg hxh).symm
    -- the three-term triangle bound
    have hA : Integrable (fun x => ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
        - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖) volume := (hcg.sub hch).norm
    have hB : Integrable (fun x => ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖)
        volume := (hch.sub hhint).norm
    have hC : Integrable (fun x => ‖h x - g x‖) volume := (hhint.sub hg).norm
    have hAB : Integrable (fun x => ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
        + ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖) volume := hA.add hB
    have hABC : Integrable (fun x => ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
        + ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖
        + ‖h x - g x‖) volume := hAB.add hC
    have hptwise : ∀ x : ℂ,
        ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - g x‖
          ≤ ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
            + ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖
            + ‖h x - g x‖ := by
      intro x
      set X := (convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x with hX
      set Y := (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x with hY
      have hre : X - g x = (X - Y) + ((Y - h x) + (h x - g x)) := by ring
      calc ‖X - g x‖ = ‖(X - Y) + ((Y - h x) + (h x - g x))‖ := by rw [hre]
        _ ≤ ‖X - Y‖ + ‖(Y - h x) + (h x - g x)‖ := norm_add_le _ _
        _ ≤ ‖X - Y‖ + (‖Y - h x‖ + ‖h x - g x‖) := by
            linarith [norm_add_le (Y - h x) (h x - g x)]
        _ = ‖X - Y‖ + ‖Y - h x‖ + ‖h x - g x‖ := by ring
    have hmono : ∫ x, ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - g x‖
        ≤ ∫ x, (‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
            + ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖
            + ‖h x - g x‖) :=
      integral_mono (hcg.sub hg).norm hABC hptwise
    have hsplit : ∫ x, (‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖
            + ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖
            + ‖h x - g x‖)
        = (∫ x, ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
              - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖)
          + (∫ x, ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖)
          + (∫ x, ‖h x - g x‖) := by
      rw [integral_add hAB hC, integral_add hA hB]
    -- first term: the L¹ contraction applied to `g - h`
    have hgh : ∫ x, ‖g x - h x‖ ≤ η / 3 := hhle
    have hfirst : ∫ x, ‖(convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
          - (convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ η / 3 := by
      rw [integral_congr_ae hlin]
      have hco := conv_l1 ((φ n).normed volume) (g - h) hρint (hg.sub hhint)
      rw [hρnorm, one_mul] at hco
      refine hco.trans ?_
      simpa [Pi.sub_apply] using hgh
    have hthird : ∫ x, ‖h x - g x‖ ≤ η / 3 := by
      simpa [norm_sub_rev] using hgh
    linarith
  have h2 := conv_cont_l1 h hhcont hhsupp φ hr1 hr0
  rw [NormedAddGroup.tendsto_nhds_zero] at h2
  filter_upwards [h2 (η / 3) (by linarith)] with n hn
  have hmid : ∫ x, ‖(convolution ((φ n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume) x - h x‖ < η / 3 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hn
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have := hkey n
  linarith
