import IwaniecManfredi.IsWeakPartialOn
import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.PartialWord

/-- The continuous representative of Section 6 of the paper: a locally
integrable function whose two distributional partial derivatives are
*continuous* on an open set agrees almost everywhere with a `C^1` function
whose classical partials are those two.  This is what turns the paper's
``$u\in C^{k,\alpha}_{loc}$'' into a true statement: `PHarmonicOn` sees `u`
only through integrals, so it cannot constrain `u` on a null set, and the
regularity conclusion must be asserted of a representative.  For `p`-harmonic
`u` the hypothesis is met because the complex gradient `f` is continuous, so
`∇u = (2 Re f, -2 Im f)` is continuous on all of `Ω`.  The instance
`F = 0` is also the constant-`u` branch. -/
theorem WeakGradContinuousRep (Ω : Set ℂ) (hΩ : IsOpen Ω) (u : ℂ → ℝ) (F : Fin 2 → ℂ → ℂ)
    (hu : MemLpLocOn 1 Ω (fun z => ((u z : ℝ) : ℂ)))
    (hF : ∀ j : Fin 2, ContinuousOn (F j) Ω)
    (hweak : ∀ j : Fin 2, IsWeakPartialOn Ω j (fun z => ((u z : ℝ) : ℂ)) (F j)) :
    ∃ w : ℂ → ℝ,
      (∀ᵐ z, z ∈ Ω → w z = u z) ∧
      ContDiffOn ℝ (1 : ℕ) (fun z => ((w z : ℝ) : ℂ)) Ω ∧
      (∀ (j : Fin 2), ∀ z ∈ Ω,
        PartialWord [j] (fun z => ((w z : ℝ) : ℂ)) z = F j z) := by
  -- ## Steps 0-5: the LOCAL representative.  The existentials are OUTSIDE the
  -- membership hypothesis so that `choose` extracts functions of `z` alone.
  have hloc : ∀ z : ℂ, ∃ (ρ : ℝ) (v : ℂ → ℝ), z ∈ Ω →
      (0 < ρ ∧ Metric.ball z ρ ⊆ Ω ∧
       (∀ᵐ x : ℂ, x ∈ Metric.ball z ρ → v x = u x) ∧
       ContDiffOn ℝ (1 : ℕ) (fun x => ((v x : ℝ) : ℂ)) (Metric.ball z ρ) ∧
       ∀ (j : Fin 2), ∀ x ∈ Metric.ball z ρ,
         PartialWord [j] (fun x => ((v x : ℝ) : ℂ)) x = F j x) := by
    -- ## Step 0: `F 0` and `F 1` are real-valued on `Ω`.  This is proved; Steps 1-5,
    -- the mollification, are the remaining gap.
    have hFreal : ∀ (j : Fin 2), ∀ z ∈ Ω, (F j z).im = 0 := by
      -- the differential of a cast real function is the cast of its differential
      have hdcast : ∀ (ψ : ℂ → ℝ) (z c : ℂ), DifferentiableAt ℝ ψ z →
          fderiv ℝ (fun x => ((ψ x : ℝ) : ℂ)) z c = ((fderiv ℝ ψ z c : ℝ) : ℂ) := by
        intro ψ z c hψ
        have h : HasFDerivAt (fun x => ((ψ x : ℝ) : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ ψ z)) z :=
          Complex.ofRealCLM.hasFDerivAt.comp z hψ.hasFDerivAt
        rw [h.fderiv]
        rfl
      -- the product `F j * ψ` is globally continuous: inside `Ω` both factors are, and
      -- outside `Ω` the cast bump vanishes on a neighbourhood
      have hprodcont : ∀ (j : Fin 2) (ψ : ℂ → ℝ), Continuous ψ →
          tsupport ψ ⊆ Ω → Continuous (fun z => F j z * ((ψ z : ℝ) : ℂ)) := by
        intro j ψ hψc hts
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hzΩ : z ∈ Ω
        · exact ((hF j).continuousAt (hΩ.mem_nhds hzΩ)).mul
            (Complex.continuous_ofReal.continuousAt.comp hψc.continuousAt)
        · have hznot : z ∉ tsupport ψ := fun h => hzΩ (hts h)
          have hev : (fun z => F j z * ((ψ z : ℝ) : ℂ)) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
            filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hznot] with x hx
            have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
            rw [this]
            simp
          exact (continuousAt_const).congr hev.symm
      have hprodsupp : ∀ (j : Fin 2) (ψ : ℂ → ℝ), HasCompactSupport ψ →
          HasCompactSupport (fun z => F j z * ((ψ z : ℝ) : ℂ)) := by
        intro j ψ hψ
        refine HasCompactSupport.intro hψ.isCompact ?_
        intro x hx
        have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [this]
        simp
      -- the vanishing of the imaginary part against every real bump
      have hkey : ∀ (j : Fin 2) (ψ : ℂ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → tsupport ψ ⊆ Ω →
          ∫ z, (F j z).im * ψ z = 0 := by
        intro j ψ hcd hcs hts
        have hcdc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((ψ x : ℝ) : ℂ)) :=
          Complex.ofRealCLM.contDiff.comp hcd
        have hcsc : HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ)) := by
          refine HasCompactSupport.intro hcs.isCompact (fun x hx => ?_)
          have : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [this]; simp
        have htsc : tsupport (fun x => ((ψ x : ℝ) : ℂ)) ⊆ Ω := by
          refine subset_trans (closure_mono ?_) hts
          intro x hx hc
          refine hx ?_
          show ((ψ x : ℝ) : ℂ) = 0
          rw [hc]; simp
        have hid := hweak j _ ⟨hcdc, hcsc, htsc⟩
        -- the left side is the cast of a real integral
        have hlhs : (∫ z, ((u z : ℝ) : ℂ)
            * fderiv ℝ (fun x => ((ψ x : ℝ) : ℂ)) z (if j = 0 then 1 else Complex.I))
            = ((∫ z, u z * fderiv ℝ ψ z (if j = 0 then 1 else Complex.I) : ℝ) : ℂ) := by
          rw [← integral_complex_ofReal]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          show ((u z : ℝ) : ℂ)
              * fderiv ℝ (fun x => ((ψ x : ℝ) : ℂ)) z (if j = 0 then 1 else Complex.I)
              = ((u z * fderiv ℝ ψ z (if j = 0 then 1 else Complex.I) : ℝ) : ℂ)
          rw [hdcast ψ z _ (hcd.differentiable (by simp) z)]
          push_cast
          ring
        rw [hlhs] at hid
        -- so the right side has zero imaginary part
        have hint : MeasureTheory.Integrable (fun z => F j z * ((ψ z : ℝ) : ℂ)) :=
          (hprodcont j ψ hcd.continuous hts).integrable_of_hasCompactSupport (hprodsupp j ψ hcs)
        have him : (∫ z, F j z * ((ψ z : ℝ) : ℂ)).im = 0 := by
          have h := congrArg Complex.im hid.symm
          simp only [Complex.neg_im, Complex.ofReal_im] at h
          linarith [h]
        have h2 := Complex.imCLM.integral_comp_comm hint
        simp only [Complex.imCLM_apply] at h2
        rw [him] at h2
        refine Eq.trans ?_ h2
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        simp [Complex.mul_im]
      -- a continuous function on `Ω` integrating to `0` against every real bump vanishes
      have hzero : ∀ g : ℂ → ℝ, ContinuousOn g Ω →
          (∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
            ∫ z, g z * ψ z = 0) → ∀ z₀ ∈ Ω, g z₀ = 0 := by
        intro g hgc hgint z₀ hz₀
        by_contra hne
        have habs : 0 < |g z₀| := abs_pos.mpr hne
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
        have hca : ContinuousAt g z₀ := hgc.continuousAt (hΩ.mem_nhds hz₀)
        obtain ⟨η, hη, hηbd⟩ := Metric.continuousAt_iff.mp hca (|g z₀| / 2) (by linarith)
        obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = min ρ η := ⟨_, rfl⟩
        have hδ : 0 < δ := by rw [hδdef]; exact lt_min hρ hη
        have hδsub : Metric.ball z₀ δ ⊆ Ω := by
          refine subset_trans (fun z hz => ?_) hρsub
          exact Metric.mem_ball.mpr
            (lt_of_lt_of_le (Metric.mem_ball.mp hz) (by rw [hδdef]; exact min_le_left _ _))
        have hsame : ∀ z ∈ Metric.ball z₀ δ, |g z₀| / 2 < |g z| := by
          intro z hz
          have h1 : dist (g z) (g z₀) < |g z₀| / 2 :=
            hηbd (lt_of_lt_of_le (Metric.mem_ball.mp hz) (by rw [hδdef]; exact min_le_right _ _))
          rw [Real.dist_eq] at h1
          have h2 : |g z₀| - |g z| ≤ |g z - g z₀| := by
            rw [abs_sub_comm]
            linarith [abs_sub_abs_le_abs_sub (g z₀) (g z)]
          linarith
        -- the bump
        obtain ⟨b, hbdef⟩ : ∃ b : ContDiffBump z₀, b = ⟨δ / 4, δ / 2, by linarith, by linarith⟩ :=
          ⟨_, rfl⟩
        have hbout : b.rOut = δ / 2 := by rw [hbdef]
        obtain ⟨ψ, hψdef⟩ : ∃ f : ℂ → ℝ, f = b.normed MeasureTheory.volume := ⟨_, rfl⟩
        have hψnn : ∀ z, 0 ≤ ψ z := by rw [hψdef]; exact b.nonneg_normed
        have hψsupp : Function.support ψ = Metric.ball z₀ (δ / 2) := by
          rw [hψdef, b.support_normed_eq, hbout]
        have hψts : tsupport ψ ⊆ Ω := by
          rw [hψdef, b.tsupport_normed_eq, hbout]
          refine subset_trans (fun z hz => ?_) hδsub
          exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
        have hψcd : ContDiff ℝ (⊤ : ℕ∞) ψ := by rw [hψdef]; exact b.contDiff_normed
        have hψcs : HasCompactSupport ψ := by rw [hψdef]; exact b.hasCompactSupport_normed
        -- the integrand has a strict sign on the support
        obtain ⟨e, hedef⟩ : ∃ x : ℝ, x = (if 0 < g z₀ then (1 : ℝ) else -1) := ⟨_, rfl⟩
        have hpos : ∀ z ∈ Metric.ball z₀ δ, 0 < e * g z := by
          intro z hz
          have h1 := hsame z hz
          have h2 : dist (g z) (g z₀) < |g z₀| / 2 :=
            hηbd (lt_of_lt_of_le (Metric.mem_ball.mp hz) (by rw [hδdef]; exact min_le_right _ _))
          rw [Real.dist_eq] at h2
          rw [hedef]
          by_cases h : 0 < g z₀
          · simp only [if_pos h, one_mul]
            rw [abs_of_pos h] at h2
            linarith [neg_abs_le (g z - g z₀), le_abs_self (g z - g z₀)]
          · simp only [if_neg h]
            have hgn : g z₀ < 0 := lt_of_le_of_ne (not_lt.mp h) hne
            rw [abs_of_neg hgn] at h2
            linarith [neg_abs_le (g z - g z₀), le_abs_self (g z - g z₀)]
        have hprodnn : ∀ z, 0 ≤ (e * g z) * ψ z := by
          intro z
          by_cases hz : z ∈ Metric.ball z₀ (δ / 2)
          · exact mul_nonneg (hpos z (Metric.mem_ball.mpr
              (lt_trans (Metric.mem_ball.mp hz) (by linarith)))).le (hψnn z)
          · have : ψ z = 0 := by
              by_contra hc
              exact hz (hψsupp ▸ hc)
            rw [this, mul_zero]
        have hIzero : ∫ z, (e * g z) * ψ z = 0 := by
          have h := hgint ψ hψcd hψcs hψts
          have hcong : ∫ z, (e * g z) * ψ z = e * ∫ z, g z * ψ z := by
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
            ring
          rw [hcong, h, mul_zero]
        have hcont2 : Continuous (fun z => (e * g z) * ψ z) := by
          rw [continuous_iff_continuousAt]
          intro z
          by_cases hzΩ : z ∈ Ω
          · exact ((continuousAt_const).mul
              (hgc.continuousAt (hΩ.mem_nhds hzΩ))).mul hψcd.continuous.continuousAt
          · have hznot : z ∉ tsupport ψ := fun h => hzΩ (hψts h)
            have hev : (fun z => (e * g z) * ψ z) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
              filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hznot] with x hx
              have hx0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
              show (e * g x) * ψ x = 0
              rw [hx0, mul_zero]
            exact continuousAt_const.congr hev.symm
        have hcs2 : HasCompactSupport (fun z => (e * g z) * ψ z) := by
          refine HasCompactSupport.intro hψcs.isCompact (fun x hx => ?_)
          have hx0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [hx0, mul_zero]
        have hint2 : MeasureTheory.Integrable (fun z => (e * g z) * ψ z) :=
          hcont2.integrable_of_hasCompactSupport hcs2
        have hsuppeq : 0 < MeasureTheory.volume
            (Function.support (fun z => (e * g z) * ψ z)) := by
          have hball : 0 < MeasureTheory.volume (Metric.ball z₀ (δ / 2)) :=
            Metric.isOpen_ball.measure_pos _ ⟨z₀, Metric.mem_ball_self (by linarith)⟩
          have hsub : Metric.ball z₀ (δ / 2)
              ⊆ Function.support (fun z => (e * g z) * ψ z) := by
            intro z hz
            have h1 : 0 < e * g z := hpos z (Metric.mem_ball.mpr
              (lt_trans (Metric.mem_ball.mp hz) (by linarith)))
            have h2 : ψ z ≠ 0 := by rw [← Function.mem_support, hψsupp]; exact hz
            show (e * g z) * ψ z ≠ 0
            exact mul_ne_zero (ne_of_gt h1) h2
          exact lt_of_lt_of_le hball (MeasureTheory.measure_mono hsub)
        have := (MeasureTheory.integral_pos_iff_support_of_nonneg hprodnn hint2).mpr hsuppeq
        rw [hIzero] at this
        exact absurd this (lt_irrefl 0)
      intro j z₀ hz₀
      exact hzero (fun z => (F j z).im) (Complex.continuous_im.comp_continuousOn (hF j))
        (fun ψ h1 h2 h3 => hkey j ψ h1 h2 h3) z₀ hz₀
    -- ## generic tools
    have hdcast : ∀ (ψ : ℂ → ℝ) (z c : ℂ), DifferentiableAt ℝ ψ z →
        fderiv ℝ (fun x => ((ψ x : ℝ) : ℂ)) z c = ((fderiv ℝ ψ z c : ℝ) : ℂ) := by
      intro ψ z c hψ
      have h : HasFDerivAt (fun x => ((ψ x : ℝ) : ℂ))
          (Complex.ofRealCLM.comp (fderiv ℝ ψ z)) z :=
        Complex.ofRealCLM.hasFDerivAt.comp z hψ.hasFDerivAt
      rw [h.fderiv]
      rfl
    have hprec : ∀ (a : ℝ) (T : ℂ →L[ℝ] ℝ) (w : ℂ),
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) a T w = a * T w := by
      intro a T w
      simp [ContinuousLinearMap.precompR_apply]
    obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ × ℝ →L[ℝ] (ℂ →L[ℝ] ℝ), ∀ (q : ℝ × ℝ) (w : ℂ),
        Θ q w = w.re * q.1 + w.im * q.2 := by
      refine ⟨(ContinuousLinearMap.smulRightL ℝ ℂ ℝ Complex.reCLM).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (ContinuousLinearMap.smulRightL ℝ ℂ ℝ Complex.imCLM).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ), ?_⟩
      intro q w
      simp [ContinuousLinearMap.smulRightL_apply_apply]
    have hopbd : ∀ T : ℂ →L[ℝ] ℝ, ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      have hdec : T w = w.re * T 1 + w.im * T Complex.I := by
        calc T w = T (w.re • (1 : ℂ) + w.im • Complex.I) := by
              congr 1
              rw [Complex.real_smul, Complex.real_smul, mul_one]
              exact (Complex.re_add_im w).symm
          _ = w.re * T 1 + w.im * T Complex.I := by
              rw [map_add, map_smul, map_smul]; simp
      rw [hdec]
      refine le_trans (norm_add_le _ _) ?_
      simp only [norm_mul, Real.norm_eq_abs]
      nlinarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w,
        abs_nonneg w.re, abs_nonneg w.im, abs_nonneg (T 1), abs_nonneg (T Complex.I)]
    have hswap : ∀ (f g : ℂ → ℝ) (x : ℂ),
        MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
          = MeasureTheory.convolution g f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
      intro f g x
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_eq_swap]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      show f t • g (x - t) = g (x - t) • f t
      simp only [smul_eq_mul]
      ring
    -- ## the real parts of `F`
    obtain ⟨fr, hfrdef⟩ : ∃ g : Fin 2 → ℂ → ℝ, g = fun j z => (F j z).re := ⟨_, rfl⟩
    have hFr : ∀ (j : Fin 2), ∀ z ∈ Ω, F j z = ((fr j z : ℝ) : ℂ) := by
      intro j z hz
      simp only [hfrdef]
      refine Complex.ext rfl ?_
      rw [Complex.ofReal_im]
      exact hFreal j z hz
    have hfrcont : ∀ j : Fin 2, ContinuousOn (fr j) Ω := by
      intro j
      simp only [hfrdef]
      exact Complex.continuous_re.comp_continuousOn (hF j)
    -- ## Step 1: the local set-up
    intro zs
    by_cases hzsΩ : zs ∈ Ω
    swap
    · exact ⟨1, u, fun h => absurd h hzsΩ⟩
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hΩ zs hzsΩ
    obtain ⟨ρ, hρdef⟩ : ∃ x : ℝ, x = R / 8 := ⟨_, rfl⟩
    have hρ : 0 < ρ := by rw [hρdef]; linarith
    have hball : ∀ s : ℝ, s ≤ 4 * ρ → Metric.closedBall zs s ⊆ Ω := by
      intro s hs z hz
      refine hRsub (Metric.mem_ball.mpr ?_)
      have h1 := Metric.mem_closedBall.mp hz
      rw [hρdef] at hs
      linarith
    have hKcΩ : Metric.closedBall zs (4 * ρ) ⊆ Ω := hball (4 * ρ) le_rfl
    have hKcm : MeasurableSet (Metric.closedBall zs (4 * ρ)) := measurableSet_closedBall
    obtain ⟨uh, huhdef⟩ : ∃ g : ℂ → ℝ,
        g = (Metric.closedBall zs (4 * ρ)).indicator u := ⟨_, rfl⟩
    obtain ⟨Fh, hFhdef⟩ : ∃ g : Fin 2 → ℂ → ℝ,
        g = fun j => (Metric.closedBall zs (4 * ρ)).indicator (fr j) := ⟨_, rfl⟩
    have huheq : ∀ z ∈ Metric.closedBall zs (4 * ρ), uh z = u z := by
      intro z hz; rw [huhdef, Set.indicator_of_mem hz]
    have huhzero : ∀ z, z ∉ Metric.closedBall zs (4 * ρ) → uh z = 0 := by
      intro z hz; rw [huhdef, Set.indicator_of_notMem hz]
    have hFheq : ∀ (j : Fin 2), ∀ z ∈ Metric.closedBall zs (4 * ρ), Fh j z = fr j z := by
      intro j z hz; simp only [hFhdef]; rw [Set.indicator_of_mem hz]
    have huhint : MeasureTheory.Integrable uh MeasureTheory.volume := by
      have h1 := hu (Metric.closedBall zs (4 * ρ)) hKcΩ (isCompact_closedBall _ _)
      have h2 : MeasureTheory.Integrable
          ((Metric.closedBall zs (4 * ρ)).indicator (fun z => ((u z : ℝ) : ℂ))) MeasureTheory.volume :=
        MeasureTheory.memLp_one_iff_integrable.mp h1
      have heq : (Metric.closedBall zs (4 * ρ)).indicator (fun z => ((u z : ℝ) : ℂ))
          = fun z => ((uh z : ℝ) : ℂ) := by
        funext z
        by_cases hz : z ∈ Metric.closedBall zs (4 * ρ)
        · rw [Set.indicator_of_mem hz, huheq z hz]
        · rw [Set.indicator_of_notMem hz, huhzero z hz, Complex.ofReal_zero]
      rw [heq] at h2
      have h4 := Complex.reCLM.integrable_comp h2
      simpa using h4
    have hFhint : ∀ j : Fin 2, MeasureTheory.Integrable (Fh j) MeasureTheory.volume := by
      intro j
      simp only [hFhdef]
      refine MeasureTheory.IntegrableOn.integrable_indicator ?_ hKcm
      exact ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
        ((hfrcont j).mono hKcΩ)
    -- ## the mollifier family: `rOut = 2 * rIn`, both tending to `0`
    have hbpex : ∀ n : ℕ, ∃ b : ContDiffBump (0 : ℂ),
        b.rIn = ρ / (2 * ((n : ℝ) + 2)) ∧ b.rOut = ρ / ((n : ℝ) + 2) := by
      intro n
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have h1 : (0:ℝ) < ρ / (2 * ((n : ℝ) + 2)) := by positivity
      refine ⟨⟨ρ / (2 * ((n : ℝ) + 2)), 2 * (ρ / (2 * ((n : ℝ) + 2))), h1, by linarith⟩, rfl, ?_⟩
      show 2 * (ρ / (2 * ((n : ℝ) + 2))) = ρ / ((n : ℝ) + 2)
      field_simp
    choose bp hbpIn hbpOut using hbpex
    obtain ⟨rn, hrndef⟩ : ∃ g : ℕ → ℂ → ℝ, g = fun n => (bp n).normed MeasureTheory.volume := ⟨_, rfl⟩
    obtain ⟨un, hundef⟩ : ∃ g : ℕ → ℂ → ℝ, g = fun n =>
        MeasureTheory.convolution uh (rn n) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := ⟨_, rfl⟩
    obtain ⟨Gn, hGndef⟩ : ∃ g : Fin 2 → ℕ → ℂ → ℝ, g = fun j n =>
        MeasureTheory.convolution (rn n) (Fh j) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := ⟨_, rfl⟩
    obtain ⟨dn, hdndef⟩ : ∃ g : ℕ → ℂ → (ℂ →L[ℝ] ℝ), g = fun n =>
        MeasureTheory.convolution uh (fderiv ℝ (rn n))
          ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) MeasureTheory.volume := ⟨_, rfl⟩
    have hrnts : ∀ n : ℕ, tsupport (rn n) = Metric.closedBall (0 : ℂ) ((bp n).rOut) := by
      intro n; rw [hrndef]; exact (bp n).tsupport_normed_eq
    have hrncd : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (rn n) := by
      intro n; rw [hrndef]; exact (bp n).contDiff_normed
    have hrnd : ∀ n : ℕ, Differentiable ℝ (rn n) :=
      fun n => (hrncd n).differentiable (by simp)
    have hrOut : ∀ n : ℕ, (bp n).rOut ≤ ρ / 2 := by
      intro n
      rw [hbpOut]
      have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      gcongr
    -- the derivative of the mollifier is continuous with compact support, hence bounded
    have hdfcont : ∀ n : ℕ, Continuous (fderiv ℝ (rn n)) :=
      fun n => (hrncd n).continuous_fderiv (by simp)
    have hdfcs : ∀ n : ℕ, HasCompactSupport (fderiv ℝ (rn n)) := by
      intro n
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((bp n).rOut)) (fun s hs => ?_)
      have hsn : s ∉ tsupport (rn n) := by rw [hrnts n]; exact hs
      have hev : rn n =ᶠ[nhds s] (fun _ => (0 : ℝ)) := by
        filter_upwards [((isClosed_tsupport (rn n)).isOpen_compl).mem_nhds hsn] with t ht
          using image_eq_zero_of_notMem_tsupport ht
      rw [hev.fderiv_eq]
      simp
    have hprec2 : ∀ (a : ℝ) (T : ℂ →L[ℝ] ℝ),
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) a T = a • T := by
      intro a T
      ext w
      simp [ContinuousLinearMap.precompR_apply]
    have hclmint : ∀ (n : ℕ) (x : ℂ), MeasureTheory.Integrable (fun t =>
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) (uh t) (fderiv ℝ (rn n) (x - t))) MeasureTheory.volume := by
      intro n x
      obtain ⟨C, hC⟩ := (hdfcs n).exists_bound_of_continuous (hdfcont n)
      simp only [hprec2]
      refine MeasureTheory.Integrable.mono' (g := fun t => ‖uh t‖ * C) (huhint.norm.mul_const C) ?_ ?_
      · exact huhint.aestronglyMeasurable.smul
          (((hdfcont n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      · refine Filter.Eventually.of_forall (fun t => ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    -- ## Step 1: `u_n` is differentiable with derivative `d_n`
    have hunfd : ∀ (n : ℕ) (x : ℂ), HasFDerivAt (un n) (dn n x) x := by
      intro n x
      simp only [hundef, hdndef, hrndef]
      exact ((bp n).hasCompactSupport_normed).hasFDerivAt_convolution_right _
        huhint.locallyIntegrable (bp n).contDiff_normed x
    -- ## Step 2: `∂_j u_n = G_{j,n}` on `ball zs (3ρ)`, through the weak identity
    have hstep2 : ∀ (n : ℕ) (j : Fin 2), ∀ x ∈ Metric.ball zs (3 * ρ),
        dn n x (if j = 0 then 1 else Complex.I) = Gn j n x := by
      intro n j x hx
      obtain ⟨φ, hφdef⟩ : ∃ g : ℂ → ℝ, g = fun s : ℂ => rn n (x - s) := ⟨_, rfl⟩
      -- the shifted mollifier is supported in `closedBall zs (4ρ)`
      have hφsupp : ∀ s : ℂ, s ∉ Metric.closedBall zs (4 * ρ) → φ s = 0 := by
        intro s hs
        simp only [hφdef]
        refine image_eq_zero_of_notMem_tsupport ?_
        rw [hrnts n]
        intro hc
        refine hs (Metric.mem_closedBall.mpr ?_)
        have h1 : ‖x - s‖ ≤ (bp n).rOut := by
          have := Metric.mem_closedBall.mp hc
          rwa [dist_zero_right] at this
        have h2 : ‖x - zs‖ < 3 * ρ := by
          have := Metric.mem_ball.mp hx; rwa [dist_eq_norm] at this
        have h3 := hrOut n
        have h4 : ‖s - zs‖ ≤ ‖x - s‖ + ‖x - zs‖ := by
          have he : s - zs = -(x - s) + (x - zs) := by ring
          rw [he]
          exact le_trans (norm_add_le _ _) (by rw [norm_neg])
        rw [dist_eq_norm]
        linarith
      have hφcd : ContDiff ℝ (⊤ : ℕ∞) φ := by
        simp only [hφdef]
        exact (hrncd n).comp (contDiff_const.sub contDiff_id)
      have hφts : tsupport φ ⊆ Metric.closedBall zs (4 * ρ) := by
        refine closure_minimal (fun s hs => ?_) Metric.isClosed_closedBall
        by_contra hc
        exact hs (hφsupp s hc)
      -- the cast test function for `Ω`
      obtain ⟨Φ, hΦdef⟩ : ∃ g : ℂ → ℂ, g = fun s => ((φ s : ℝ) : ℂ) := ⟨_, rfl⟩
      have hΦzero : ∀ s : ℂ, s ∉ Metric.closedBall zs (4 * ρ) → Φ s = 0 := by
        intro s hs
        simp only [hΦdef]
        rw [hφsupp s hs, Complex.ofReal_zero]
      have hΦtest : IsTestFn Ω Φ := by
        refine ⟨?_, ?_, ?_⟩
        · simp only [hΦdef]; exact Complex.ofRealCLM.contDiff.comp hφcd
        · exact HasCompactSupport.intro (isCompact_closedBall zs (4 * ρ)) hΦzero
        · refine subset_trans (closure_minimal (fun s hs => ?_) Metric.isClosed_closedBall) hKcΩ
          by_contra hc
          exact hs (hΦzero s hc)
      have hid := hweak j Φ hΦtest
      -- both sides of the weak identity are casts of real integrals
      have hL : (∫ z, ((u z : ℝ) : ℂ) * fderiv ℝ Φ z (if j = 0 then 1 else Complex.I))
          = ((∫ z, u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        show ((u z : ℝ) : ℂ) * fderiv ℝ Φ z (if j = 0 then 1 else Complex.I)
            = ((u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I) : ℝ) : ℂ)
        rw [hΦdef, hdcast φ z _ (hφcd.differentiable (by simp) z)]
        push_cast
        ring
      have hRr : (∫ z, F j z * Φ z) = ((∫ z, Fh j z * φ z : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        show F j z * Φ z = ((Fh j z * φ z : ℝ) : ℂ)
        by_cases hz : z ∈ Metric.closedBall zs (4 * ρ)
        · rw [hFr j z (hKcΩ hz), hFheq j z hz, hΦdef]
          push_cast
          ring
        · rw [hΦzero z hz, hφsupp z hz, mul_zero, mul_zero, Complex.ofReal_zero]
      rw [hL, hRr] at hid
      have hreal : (∫ z, u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I))
          = -(∫ z, Fh j z * φ z) := by
        rw [← Complex.ofReal_neg] at hid
        exact Complex.ofReal_inj.mp hid
      -- `u` may be replaced by `uh`: off `closedBall zs (4ρ)` the differential vanishes
      have hu2 : (∫ z, uh z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I))
          = (∫ z, u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I)) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        show uh z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I)
            = u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I)
        by_cases hz : z ∈ Metric.closedBall zs (4 * ρ)
        · rw [huheq z hz]
        · have hev : φ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
            filter_upwards [(Metric.isClosed_closedBall (x := zs) (ε := 4 * ρ)).isOpen_compl.mem_nhds hz]
              with t ht using hφsupp t ht
          have hdz : fderiv ℝ φ z = 0 := by rw [hev.fderiv_eq]; simp
          rw [hdz]
          simp
      -- the chain rule in the MeasureTheory.convolution variable, and its sign
      have hchain : ∀ t : ℂ, fderiv ℝ φ t (if j = 0 then 1 else Complex.I)
          = -(fderiv ℝ (rn n) (x - t) (if j = 0 then 1 else Complex.I)) := by
        intro t
        have h1 : HasFDerivAt (fun s : ℂ => x - s) (-(ContinuousLinearMap.id ℝ ℂ)) t := by
          have h0 : HasFDerivAt (fun s : ℂ => x - s)
              ((0 : ℂ →L[ℝ] ℂ) - ContinuousLinearMap.id ℝ ℂ) t :=
            (hasFDerivAt_const x t).sub (hasFDerivAt_id t)
          simpa using h0
        have h2 : HasFDerivAt φ ((fderiv ℝ (rn n) (x - t)).comp
            (-(ContinuousLinearMap.id ℝ ℂ))) t := by
          simp only [hφdef]
          exact ((hrnd n (x - t)).hasFDerivAt).comp t h1
        rw [h2.fderiv]
        simp
      -- the two convolutions, written as integrals
      have hdnval : dn n x (if j = 0 then 1 else Complex.I)
          = ∫ t, uh t * (fderiv ℝ (rn n) (x - t) (if j = 0 then 1 else Complex.I)) := by
        simp only [hdndef]
        rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply (hclmint n x)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        exact hprec (uh t) (fderiv ℝ (rn n) (x - t)) _
      have hGnval : Gn j n x = ∫ t, Fh j t * φ t := by
        simp only [hGndef]
        rw [hswap (rn n) (Fh j) x, MeasureTheory.convolution_def]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        show Fh j t • rn n (x - t) = Fh j t * φ t
        simp only [hφdef, smul_eq_mul]
      have hfin : (∫ t, uh t * (fderiv ℝ (rn n) (x - t) (if j = 0 then 1 else Complex.I)))
          = -(∫ t, uh t * fderiv ℝ φ t (if j = 0 then 1 else Complex.I)) := by
        rw [← MeasureTheory.integral_neg]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        show uh t * (fderiv ℝ (rn n) (x - t) (if j = 0 then 1 else Complex.I))
            = -(uh t * fderiv ℝ φ t (if j = 0 then 1 else Complex.I))
        rw [hchain t]
        ring
      rw [hdnval, hGnval, hfin, hu2, hreal]
      ring
    -- the outer radii tend to `0`
    have hrOuttend : Filter.Tendsto (fun n : ℕ => (bp n).rOut) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun n : ℕ => ρ / ((n : ℝ) + 2)) Filter.atTop (nhds 0) :=
        Filter.Tendsto.const_div_atTop
          (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop) ρ
      exact h.congr (fun n => (hbpOut n).symm)
    have hbΩ : Metric.ball zs (2 * ρ) ⊆ Ω :=
      subset_trans Metric.ball_subset_closedBall (hball (2 * ρ) (by linarith))
    have hc4 : ∀ s : ℝ, s ≤ 4 * ρ → Metric.closedBall zs s ⊆ Metric.closedBall zs (4 * ρ) :=
      fun s hs => Metric.closedBall_subset_closedBall hs
    -- ## Step 3: `G_{j,n} → F_j` uniformly on `closedBall zs (2ρ)`
    have hstep3 : ∀ (j : Fin 2) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
        ∀ x ∈ Metric.closedBall zs (2 * ρ), |Gn j n x - fr j x| ≤ ε := by
      intro j ε hε
      have hK3Ω : Metric.closedBall zs (3 * ρ) ⊆ Ω := hball (3 * ρ) (by linarith)
      obtain ⟨δ, hδ, hδb⟩ := (Metric.uniformContinuousOn_iff.mp
        ((isCompact_closedBall zs (3 * ρ)).uniformContinuousOn_of_continuous
          ((hfrcont j).mono hK3Ω))) ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hrOuttend.eventually (gt_mem_nhds hδ))
      refine ⟨N, fun n hn x hx => ?_⟩
      have hrd : (bp n).rOut < δ := hN n hn
      have h2 := Metric.mem_closedBall.mp hx
      have h3 := hrOut n
      have hx3 : x ∈ Metric.closedBall zs (3 * ρ) :=
        Metric.mem_closedBall.mpr (by linarith)
      have hx4 : x ∈ Metric.closedBall zs (4 * ρ) :=
        Metric.mem_closedBall.mpr (by linarith)
      have hg : ∀ y ∈ Metric.ball x ((bp n).rOut), dist (Fh j y) (Fh j x) ≤ ε := by
        intro y hy
        have h1 := Metric.mem_ball.mp hy
        have htri := dist_triangle y x zs
        have hy3 : y ∈ Metric.closedBall zs (3 * ρ) := Metric.mem_closedBall.mpr (by linarith)
        have hy4 : y ∈ Metric.closedBall zs (4 * ρ) := Metric.mem_closedBall.mpr (by linarith)
        rw [hFheq j y hy4, hFheq j x hx4]
        exact (hδb y hy3 x hx3 (lt_trans h1 hrd)).le
      have hdc := (bp n).dist_normed_convolution_le (hFhint j).aestronglyMeasurable hg
      rw [Real.dist_eq, hFheq j x hx4] at hdc
      have hGnx : Gn j n x
          = MeasureTheory.convolution ((bp n).normed MeasureTheory.volume) (Fh j) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
        simp only [hGndef, hrndef]
      rw [hGnx]
      exact hdc
    -- ## the limit differential `Lm`
    have hfin2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    obtain ⟨Lm, hLmdef⟩ : ∃ g : ℂ → (ℂ →L[ℝ] ℝ), g = fun x => Θ (fr 0 x, fr 1 x) := ⟨_, rfl⟩
    have hLm0 : ∀ x : ℂ, Lm x 1 = fr 0 x := by
      intro x; simp only [hLmdef]; rw [hΘ]; simp
    have hLm1 : ∀ x : ℂ, Lm x Complex.I = fr 1 x := by
      intro x; simp only [hLmdef]; rw [hΘ]; simp
    have hLmval : ∀ (x : ℂ) (j : Fin 2),
        Lm x (if j = 0 then 1 else Complex.I) = fr j x := by
      intro x j
      rcases hfin2 j with hj | hj <;> subst hj
      · simpa using hLm0 x
      · simpa using hLm1 x
    have hstep2' : ∀ (n : ℕ), ∀ x ∈ Metric.ball zs (3 * ρ),
        dn n x 1 = Gn 0 n x ∧ dn n x Complex.I = Gn 1 n x := by
      intro n x hx
      refine ⟨?_, ?_⟩
      · have h := hstep2 n 0 x hx; simpa using h
      · have h := hstep2 n 1 x hx; simpa using h
    -- the uniform estimate on the differentials
    have hdnconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
        ∀ x ∈ Metric.closedBall zs (2 * ρ), ‖dn n x - Lm x‖ ≤ ε := by
      intro ε hε
      obtain ⟨N0, hN0⟩ := hstep3 0 (ε / 2) (by linarith)
      obtain ⟨N1, hN1⟩ := hstep3 1 (ε / 2) (by linarith)
      refine ⟨max N0 N1, fun n hn x hx => ?_⟩
      have h0 := hN0 n (le_trans (le_max_left _ _) hn) x hx
      have h1 := hN1 n (le_trans (le_max_right _ _) hn) x hx
      have hx3 : x ∈ Metric.ball zs (3 * ρ) := by
        refine Metric.mem_ball.mpr ?_
        have := Metric.mem_closedBall.mp hx
        linarith
      obtain ⟨hs0, hs1⟩ := hstep2' n x hx3
      have hb := hopbd (dn n x - Lm x)
      have e0 : (dn n x - Lm x) 1 = Gn 0 n x - fr 0 x := by rw [sub_apply, hs0, hLm0 x]
      have e1 : (dn n x - Lm x) Complex.I = Gn 1 n x - fr 1 x := by rw [sub_apply, hs1, hLm1 x]
      rw [e0, e1] at hb
      simp only [Real.norm_eq_abs] at hb
      linarith
    -- ## Step 4: `u_n → u` almost everywhere
    have hae4 : ∀ᵐ x : ℂ, Filter.Tendsto (fun n => un n x) Filter.atTop (nhds (uh x)) := by
      have hK : ∀ᶠ n in Filter.atTop, (bp n).rOut ≤ 2 * (bp n).rIn := by
        refine Filter.Eventually.of_forall (fun n => ?_)
        have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
        rw [hbpOut, hbpIn]
        refine le_of_eq ?_
        field_simp
      have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := bp) (l := Filter.atTop) (K := 2) (μ := MeasureTheory.volume) hrOuttend hK
        huhint.locallyIntegrable
      filter_upwards [h] with x hx
      refine hx.congr (fun n => ?_)
      simp only [hundef, hrndef]
      exact (hswap uh ((bp n).normed MeasureTheory.volume) x).symm
    -- ## Step 5: the base point, the uniform Cauchy property, and the limit
    have hUpos : 0 < MeasureTheory.volume (Metric.ball zs (2 * ρ)) :=
      Metric.isOpen_ball.measure_pos _ ⟨zs, Metric.mem_ball_self (by linarith)⟩
    obtain ⟨z₁, hz₁U, hz₁conv⟩ : ∃ z ∈ Metric.ball zs (2 * ρ),
        Filter.Tendsto (fun n => un n z) Filter.atTop (nhds (uh z)) := by
      by_contra hc
      refine hUpos.ne' (MeasureTheory.measure_mono_null (fun x hx => ?_) (MeasureTheory.ae_iff.mp hae4))
      exact fun hconv => hc ⟨x, hx, hconv⟩
    have hcauchy : ∀ x ∈ Metric.ball zs (2 * ρ), CauchySeq (fun n => un n x) := by
      intro x hx
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N1, hN1⟩ := hdnconv (ε / (3 * (4 * ρ + 1))) (by positivity)
      obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hz₁conv (ε / 6) (by linarith)
      refine ⟨max N1 N2, fun m hm n hn => ?_⟩
      have hm1 := le_trans (le_max_left N1 N2) hm
      have hm2 := le_trans (le_max_right N1 N2) hm
      have hn1 := le_trans (le_max_left N1 N2) hn
      have hn2 := le_trans (le_max_right N1 N2) hn
      -- the derivative difference is uniformly small on the convex `closedBall zs (2ρ)`
      have hbd : ∀ y ∈ Metric.closedBall zs (2 * ρ),
          ‖dn m y - dn n y‖ ≤ 2 * (ε / (3 * (4 * ρ + 1))) := by
        intro y hy
        have ha := hN1 m hm1 y hy
        have hb := hN1 n hn1 y hy
        have : dn m y - dn n y = (dn m y - Lm y) - (dn n y - Lm y) := by abel
        rw [this]
        exact le_trans (norm_sub_le _ _) (by linarith)
      have hfdw : ∀ y ∈ Metric.closedBall zs (2 * ρ),
          HasFDerivWithinAt (fun w => un m w - un n w) (dn m y - dn n y)
            (Metric.closedBall zs (2 * ρ)) y := by
        intro y _
        have h0 : HasFDerivAt (fun w => un m w - un n w) (dn m y - dn n y) y :=
          (hunfd m y).sub (hunfd n y)
        exact h0.hasFDerivWithinAt
      have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hfdw hbd
        (convex_closedBall zs (2 * ρ)) (Metric.ball_subset_closedBall hz₁U)
        (Metric.ball_subset_closedBall hx)
      have hdxz : ‖x - z₁‖ ≤ 4 * ρ := by
        have h1 := Metric.mem_ball.mp hx
        have h2 := Metric.mem_ball.mp hz₁U
        have h3 := dist_triangle x zs z₁
        rw [← dist_eq_norm]
        rw [dist_comm zs z₁] at h3
        linarith
      have hz1m := hN2 m hm2
      have hz1n := hN2 n hn2
      rw [Real.dist_eq] at hz1m hz1n ⊢
      have hkey : |un m x - un n x| ≤ |un m z₁ - un n z₁|
          + 2 * (ε / (3 * (4 * ρ + 1))) * ‖x - z₁‖ := by
        have hsplit : un m x - un n x
            = (un m z₁ - un n z₁) + ((un m x - un n x) - (un m z₁ - un n z₁)) := by ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) ?_
        have : |un m x - un n x - (un m z₁ - un n z₁)|
            ≤ 2 * (ε / (3 * (4 * ρ + 1))) * ‖x - z₁‖ := by
          have := hmv
          rw [Real.norm_eq_abs] at this
          exact this
        linarith
      have hz1 : |un m z₁ - un n z₁| < ε / 3 := by
        have h1 : |un m z₁ - uh z₁| < ε / 6 := hz1m
        have h2 : |un n z₁ - uh z₁| < ε / 6 := hz1n
        rw [abs_lt] at h1 h2
        rw [abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have hfac : 2 * (ε / (3 * (4 * ρ + 1))) * ‖x - z₁‖ ≤ 2 * ε / 3 := by
        obtain ⟨c, hcdef⟩ : ∃ y : ℝ, y = ε / (3 * (4 * ρ + 1)) := ⟨_, rfl⟩
        have hcpos : 0 < c := by rw [hcdef]; positivity
        have hc : c * (3 * (4 * ρ + 1)) = ε := by
          rw [hcdef]
          field_simp
        rw [← hcdef]
        nlinarith [mul_nonneg hcpos.le (by linarith : (0:ℝ) ≤ 4 * ρ - ‖x - z₁‖), hcpos.le]
      linarith
    obtain ⟨v, hv⟩ : ∃ g : ℂ → ℝ, ∀ x : ℂ, x ∈ Metric.ball zs (2 * ρ) →
        Filter.Tendsto (fun n => un n x) Filter.atTop (nhds (g x)) := by
      have hex : ∀ x : ℂ, ∃ r : ℝ, x ∈ Metric.ball zs (2 * ρ) →
          Filter.Tendsto (fun n => un n x) Filter.atTop (nhds r) := by
        intro x
        by_cases hx : x ∈ Metric.ball zs (2 * ρ)
        · obtain ⟨r, hr⟩ := cauchySeq_tendsto_of_complete (hcauchy x hx)
          exact ⟨r, fun _ => hr⟩
        · exact ⟨0, fun h => absurd h hx⟩
      choose v hv using hex
      exact ⟨v, hv⟩
    have htlu : TendstoLocallyUniformlyOn dn Lm Filter.atTop (Metric.ball zs (2 * ρ)) := by
      refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hdnconv (ε / 2) (by linarith)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn x hx
      have h := hN n hn x (Metric.ball_subset_closedBall hx)
      rw [dist_eq_norm, ← norm_neg]
      have hne : -(Lm x - dn n x) = dn n x - Lm x := by abel
      rw [hne]
      linarith
    have hfdv : ∀ x ∈ Metric.ball zs (2 * ρ), HasFDerivAt v (Lm x) x := fun x hx =>
      hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball htlu
        (fun n y hy => hunfd n y) (fun y hy => hv y hy) hx
    have hfdc : ∀ x ∈ Metric.ball zs (2 * ρ),
        HasFDerivAt (fun y => ((v y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (Lm x)) x := fun x hx =>
      Complex.ofRealCLM.hasFDerivAt.comp x (hfdv x hx)
    have hLmcont : ContinuousOn Lm (Metric.ball zs (2 * ρ)) := by
      simp only [hLmdef]
      exact Θ.continuous.comp_continuousOn
        (((hfrcont 0).mono hbΩ).prodMk ((hfrcont 1).mono hbΩ))
    -- ## assembly
    refine ⟨2 * ρ, v, fun _ => ⟨by linarith, hbΩ, ?_, ?_, ?_⟩⟩
    · filter_upwards [hae4] with x hx hxU
      have h1 := hv x hxU
      have h2 : uh x = u x :=
        huheq x (hc4 (2 * ρ) (by linarith) (Metric.ball_subset_closedBall hxU))
      rw [← h2]
      exact tendsto_nhds_unique h1 hx
    · rw [show ((1 : ℕ) : WithTop ℕ∞) = 0 + 1 from by norm_num,
        contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
      refine ⟨fun x hx => ((hfdc x hx).differentiableAt).differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      rw [contDiffOn_zero]
      have hco : ContinuousOn (fun x => Complex.ofRealCLM.comp (Lm x))
          (Metric.ball zs (2 * ρ)) :=
        ((ContinuousLinearMap.compL ℝ ℂ ℝ ℂ) Complex.ofRealCLM).continuous.comp_continuousOn
          hLmcont
      exact hco.congr (fun x hx => (hfdc x hx).fderiv)
    · intro j x hx
      show fderiv ℝ (fun y => ((v y : ℝ) : ℂ)) x (if j = 0 then 1 else Complex.I) = F j x
      rw [(hfdc x hx).fderiv, hFr j x (hbΩ hx)]
      show ((Lm x (if j = 0 then 1 else Complex.I) : ℝ) : ℂ) = ((fr j x : ℝ) : ℂ)
      rw [hLmval x j]
  choose rr vv hvv using hloc
  -- ## Shared tool: two continuous functions agreeing a.e. on an OPEN set agree
  -- everywhere on it.  (The `FourierCoefOde:386-410` block, lifted to `ℂ → ℂ`.)
  have hagree : ∀ (S : Set ℂ) (G1 G2 : ℂ → ℂ), IsOpen S →
      ContinuousOn G1 S → ContinuousOn G2 S →
      (∀ᵐ x : ℂ, x ∈ S → G1 x = G2 x) → ∀ x ∈ S, G1 x = G2 x := by
    intro S G1 G2 hS h1 h2 hae x hx
    by_contra hne
    have hEopen : IsOpen {y : ℂ | y ∈ S ∧ G1 y ≠ G2 y} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨hymem, hyne⟩ := hy
      have hd : ContinuousAt (fun t => G1 t - G2 t) y :=
        (h1.continuousAt (hS.mem_nhds hymem)).sub (h2.continuousAt (hS.mem_nhds hymem))
      filter_upwards [hS.mem_nhds hymem, hd.eventually_ne (sub_ne_zero.mpr hyne)]
        with t ht1 ht2
      exact ⟨ht1, sub_ne_zero.mp ht2⟩
    have hE0 : MeasureTheory.volume {y : ℂ | y ∈ S ∧ G1 y ≠ G2 y} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro y hy
      exact fun hcon => hy.2 (hcon hy.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨x, hx, hne⟩).ne' hE0
  -- ## Step 6: the canonical global value is the LOCAL representative CENTRED at `z`,
  -- evaluated at `z`.  No Lebesgue average, no `limUnder`, no `Nonempty` instance.
  obtain ⟨w, hwdef⟩ : ∃ g : ℂ → ℝ, g = fun z => vv z z := ⟨_, rfl⟩
  -- (7): `w` agrees with every local representative on that representative's ball
  have hpatch : ∀ z₀ ∈ Ω, ∀ z ∈ Metric.ball z₀ (rr z₀), w z = vv z₀ z := by
    intro z₀ hz₀ z hz
    obtain ⟨hρ0, hsub0, hae0, hcd0, hpd0⟩ := hvv z₀ hz₀
    obtain ⟨hρz, hsubz, haez, hcdz, hpdz⟩ := hvv z (hsub0 hz)
    have hSo : IsOpen (Metric.ball z (rr z) ∩ Metric.ball z₀ (rr z₀)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have hzS : z ∈ Metric.ball z (rr z) ∩ Metric.ball z₀ (rr z₀) :=
      ⟨Metric.mem_ball_self hρz, hz⟩
    have heq := hagree _ (fun x => ((vv z x : ℝ) : ℂ)) (fun x => ((vv z₀ x : ℝ) : ℂ)) hSo
      (hcdz.continuousOn.mono Set.inter_subset_left)
      (hcd0.continuousOn.mono Set.inter_subset_right)
      (by
        filter_upwards [haez, hae0] with x h1 h2
        intro hxS
        rw [h1 hxS.1, h2 hxS.2])
      z hzS
    simp only [hwdef]
    exact Complex.ofReal_inj.mp heq
  -- ## Step 7, (b): `C^1` on `Ω`, by locality
  have hcdw : ContDiffOn ℝ (1 : ℕ) (fun z => ((w z : ℝ) : ℂ)) Ω := by
    refine contDiffOn_of_locally_contDiffOn (fun z₀ hz₀ => ?_)
    obtain ⟨hρ0, hsub0, hae0, hcd0, hpd0⟩ := hvv z₀ hz₀
    refine ⟨Metric.ball z₀ (rr z₀), Metric.isOpen_ball, Metric.mem_ball_self hρ0, ?_⟩
    rw [Set.inter_eq_self_of_subset_right hsub0]
    refine hcd0.congr (fun x hx => ?_)
    show ((w x : ℝ) : ℂ) = ((vv z₀ x : ℝ) : ℂ)
    rw [hpatch z₀ hz₀ x hx]
  -- ## Step 7, (c): the classical partials, through `EventuallyEq.fderiv_eq`
  have hpdw : ∀ (j : Fin 2), ∀ z ∈ Ω,
      PartialWord [j] (fun z => ((w z : ℝ) : ℂ)) z = F j z := by
    intro j z₀ hz₀
    obtain ⟨hρ0, hsub0, hae0, hcd0, hpd0⟩ := hvv z₀ hz₀
    have hev : (fun z => ((w z : ℝ) : ℂ)) =ᶠ[nhds z₀] (fun x => ((vv z₀ x : ℝ) : ℂ)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0)] with x hx
      show ((w x : ℝ) : ℂ) = ((vv z₀ x : ℝ) : ℂ)
      rw [hpatch z₀ hz₀ x hx]
    show fderiv ℝ (fun z => ((w z : ℝ) : ℂ)) z₀ (if j = 0 then 1 else Complex.I) = F j z₀
    rw [hev.fderiv_eq]
    exact hpd0 j z₀ (Metric.mem_ball_self hρ0)
  -- ## Step 7, (a): the a.e. identity on `Ω`, by a COUNTABLE subcover
  have haew : ∀ᵐ z : ℂ, z ∈ Ω → w z = u z := by
    obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : ↥Ω => Metric.ball i.1 (rr i.1)) (fun _ => Metric.isOpen_ball)
    have hTcount : Countable ↥T := hTc.to_subtype
    have hall : ∀ᵐ x : ℂ, ∀ i : ↥T, x ∈ Metric.ball i.1.1 (rr i.1.1) → w x = u x := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      obtain ⟨hρ0, hsub0, hae0, hcd0, hpd0⟩ := hvv i.1.1 i.1.2
      filter_upwards [hae0] with x hx hxb
      rw [hpatch i.1.1 i.1.2 x hxb]
      exact hx hxb
    filter_upwards [hall] with x hx hxΩ
    have hmem : x ∈ ⋃ i : ↥Ω, Metric.ball i.1 (rr i.1) :=
      Set.mem_iUnion.mpr ⟨⟨x, hxΩ⟩, Metric.mem_ball_self (hvv x hxΩ).1⟩
    rw [← hTeq] at hmem
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.mp hmem
    exact hx ⟨i, hiT⟩ hxi
  exact ⟨w, haew, hcdw, hpdw⟩
