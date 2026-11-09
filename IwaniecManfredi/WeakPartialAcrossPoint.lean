import IwaniecManfredi.IsWeakPartialOn
import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.PartialWord
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
set_option maxHeartbeats 400000

/-- A classical partial derivative off a locally finite exceptional set is the
distributional partial derivative on the whole open set, provided the function
grows near each exceptional point slower than the first power of the distance
to it.  This is the step hidden in Section 6's "Hence `u ∈ W^{k+2,q}_loc(Ω)`"
(`paper.tex:534`): the derivatives of the regular representative are classical
only off the singular set, where they blow up like `|z|^{α-2}`, and the cutoff
boundary term is `O(ε^{1-β})`.  The same statement is what carries Section 7's
classical `p`-harmonic identity off the origin to the weak form that
`PHarmonicOn` demands, with `β = 0` there since `|f|^{p-2}f → 0`; a single
exceptional point, which is the case the name recalls, is `S = {z₀}`. -/
theorem WeakPartialAcrossPoint (Ω : Set ℂ) (hΩ : IsOpen Ω) (S : Set ℂ) (hSΩ : S ⊆ Ω)
    (hSfin : ∀ Kc ⊆ Ω, IsCompact Kc → (S ∩ Kc).Finite)
    (j : Fin 2) (g v : ℂ → ℂ) (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hg : ContDiffOn ℝ (1 : ℕ) g (Ω \ S))
    (hv : ∀ z ∈ Ω \ S, PartialWord [j] g z = v z)
    (hgloc : MemLpLocOn 1 Ω g)
    (hvloc : MemLpLocOn 1 Ω v)
    (hgrow : ∀ z₀ ∈ S, ∃ M ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < ρ →
      ‖g z‖ ≤ M * ‖z - z₀‖ ^ (-β)) :
    IsWeakPartialOn Ω j g v := by
  set e : ℂ := if j = 0 then 1 else Complex.I with hedef
  have hene : ‖e‖ = 1 := by rw [hedef]; split <;> simp
  -- STEP 0a: `Ω \ S` is open, because `S` is locally finite in `Ω`
  have hopen : IsOpen (Ω \ S) := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ z hz.1
    have hcb : Metric.closedBall z (r / 2) ⊆ Ω := by
      intro w hw
      exact hrΩ (Metric.mem_ball.mpr
        (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)))
    have hfin : (S ∩ Metric.closedBall z (r / 2)).Finite :=
      hSfin _ hcb (isCompact_closedBall _ _)
    have hzn : z ∉ S ∩ Metric.closedBall z (r / 2) := fun h => hz.2 h.1
    obtain ⟨r2, hr2, hr2sub⟩ :=
      Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl z hzn
    refine ⟨min (r / 2) r2, lt_min (by linarith) hr2, ?_⟩
    intro w hw
    have hw1 : w ∈ Metric.closedBall z (r / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
    refine ⟨hcb hw1, fun hwS => ?_⟩
    exact hr2sub (Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right _ _))) ⟨hwS, hw1⟩
  have hgC1 : ∀ z ∈ Ω \ S, ContDiffAt ℝ (1 : ℕ) g z :=
    fun z hz => hg.contDiffAt (hopen.mem_nhds hz)
  have hgdiff : ∀ z ∈ Ω \ S, DifferentiableAt ℝ g z :=
    fun z hz => (hgC1 z hz).differentiableAt (by norm_num)
  have hgfd : ∀ z ∈ Ω \ S, fderiv ℝ g z e = v z := by
    intro z hz
    have h1 : PartialWord [j] g z = fderiv ℝ g z e := by
      simp [PartialWord, hedef]
    rw [← h1]
    exact hv z hz
  -- STEP 1a: the fixed radial cutoff profile
  set Θ : ℂ → ℝ := fun w => Real.smoothTransition (‖w‖ ^ 2 - 1) with hΘdef
  have hΘsm : ContDiff ℝ (1 : ℕ) Θ := by
    rw [hΘdef]
    exact Real.smoothTransition.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)
  have hΘ0 : ∀ w : ℂ, ‖w‖ ≤ 1 → Θ w = 0 := by
    intro w hw
    rw [hΘdef]
    exact Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg w])
  have hΘ1 : ∀ w : ℂ, 2 ≤ ‖w‖ ^ 2 → Θ w = 1 := by
    intro w hw
    rw [hΘdef]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hΘnn : ∀ w : ℂ, 0 ≤ Θ w := fun w => Real.smoothTransition.nonneg _
  have hΘle : ∀ w : ℂ, Θ w ≤ 1 := fun w => Real.smoothTransition.le_one _
  have hnsq : Continuous (fun u : ℂ => ‖u‖ ^ 2) := continuous_norm.pow 2
  have hdΘ0 : ∀ w : ℂ, (‖w‖ ^ 2 < 1 ∨ 2 < ‖w‖ ^ 2) → fderiv ℝ Θ w = 0 := by
    intro w hw
    rcases hw with h | h
    · have hU : IsOpen {u : ℂ | ‖u‖ ^ 2 < 1} := isOpen_lt hnsq continuous_const
      have hev : Θ =ᶠ[nhds w] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hU.mem_nhds h) fun u hu =>
          hΘ0 u (by simp only [Set.mem_ofPred_eq] at hu; nlinarith [norm_nonneg u])
      rw [Filter.EventuallyEq.fderiv_eq hev]
      simp
    · have hU : IsOpen {u : ℂ | 2 < ‖u‖ ^ 2} := isOpen_lt continuous_const hnsq
      have hev : Θ =ᶠ[nhds w] (fun _ => (1 : ℝ)) :=
        Filter.eventually_of_mem (hU.mem_nhds h) fun u hu =>
          hΘ1 u (le_of_lt hu)
      rw [Filter.EventuallyEq.fderiv_eq hev]
      simp
  have hdΘcont : Continuous (fderiv ℝ Θ) := (contDiff_one_iff_fderiv.mp hΘsm).2
  have hdΘsupp : HasCompactSupport (fderiv ℝ Θ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact hdΘ0 w (Or.inr (by nlinarith [not_le.mp hw]))
  obtain ⟨B, hB⟩ := hdΘcont.bounded_above_of_compact_support hdΘsupp
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  -- STEP 2a: the divergence identity for a `C¹` function of compact support
  have ftc : ∀ F : ℂ → ℂ, ContDiff ℝ (1 : ℕ) F → HasCompactSupport F →
      (∫ z, fderiv ℝ F z e) = 0 := by
    intro F hF hFc
    have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
    have hFfdc : Continuous (fderiv ℝ F) := (contDiff_one_iff_fderiv.mp hF).2
    obtain ⟨C, hC⟩ := hFfdc.bounded_above_of_compact_support
      (HasCompactSupport.fderiv (𝕜 := ℝ) hFc)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hFint : MeasureTheory.Integrable F MeasureTheory.volume := hF.continuous.integrable_of_hasCompactSupport hFc
    set Kc : Set ℂ := Metric.cthickening 1 (tsupport F) with hKcdef
    have hKccomp : IsCompact Kc := hFc.cthickening
    have hKcmeas : MeasurableSet Kc := hKccomp.isClosed.measurableSet
    set t : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1) with htdef
    have htpos : ∀ l, 0 < t l := by intro l; rw [htdef]; positivity
    have htle : ∀ l, t l ≤ 1 := by
      intro l
      have h0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      have hp : (0 : ℝ) < (l : ℝ) + 1 := by linarith
      rw [htdef]
      exact (div_le_one hp).mpr (by linarith)
    have hmvt : ∀ (s : ℝ) (z : ℂ), ‖F (z + s • e) - F z‖ ≤ C * |s| := by
      intro s z
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := F) (s := Set.univ) (C := C)
        (fun x _ => hFd x) (fun x _ => hC x) convex_univ (Set.mem_univ z)
        (Set.mem_univ (z + s • e))
      simpa [norm_smul, hene] using h
    have hzero : ∀ l, (∫ z, (t l)⁻¹ • (F (z + t l • e) - F z)) = 0 := by
      intro l
      rw [MeasureTheory.integral_smul, MeasureTheory.integral_sub (hFint.comp_add_right _) hFint,
        MeasureTheory.integral_add_right_eq_self F (t l • e), sub_self, smul_zero]
    have hdom : ∀ (l : ℕ) (z : ℂ),
        ‖(t l)⁻¹ • (F (z + t l • e) - F z)‖ ≤ Kc.indicator (fun _ => C) z := by
      intro l z
      by_cases hz : z ∈ Kc
      · rw [Set.indicator_of_mem hz, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (htpos l))]
        calc (t l)⁻¹ * ‖F (z + t l • e) - F z‖
            ≤ (t l)⁻¹ * (C * |t l|) :=
              mul_le_mul_of_nonneg_left (hmvt (t l) z) (le_of_lt (inv_pos.mpr (htpos l)))
          _ = C := by
              rw [abs_of_pos (htpos l), mul_comm C (t l), ← mul_assoc,
                inv_mul_cancel₀ (htpos l).ne', one_mul]
      · rw [Set.indicator_of_notMem hz]
        have h1 : F z = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hz (Metric.self_subset_cthickening (tsupport F) h)
        have h2 : F (z + t l • e) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun h => hz ?_
          rw [hKcdef]
          refine Metric.mem_cthickening_of_dist_le z (z + t l • e) 1 _ h ?_
          have hzz : z - (z + t l • e) = -(t l • e) := by ring
          rw [dist_eq_norm, hzz, norm_neg, norm_smul, Real.norm_eq_abs, hene, mul_one,
            abs_of_pos (htpos l)]
          exact htle l
        rw [h1, h2]
        simp
    have hlim : ∀ z : ℂ, Filter.Tendsto
        (fun l => (t l)⁻¹ • (F (z + t l • e) - F z)) Filter.atTop
        (nhds (fderiv ℝ F z e)) := by
      intro z
      have h1 : HasDerivAt (fun s : ℝ => z + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
      have h2 : HasDerivAt (fun s : ℝ => F (z + s • e))
          (fderiv ℝ F (z + (0 : ℝ) • e) e) 0 :=
        HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ))
          (hl := (hFd (z + (0 : ℝ) • e)).hasFDerivAt) (hf := h1)
      have h3 : HasDerivAt (fun s : ℝ => F (z + s • e)) (fderiv ℝ F z e) 0 := by
        simpa using h2
      rw [hasDerivAt_iff_tendsto_slope] at h3
      have h4 : Filter.Tendsto t Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ?_ ?_
        · have hone : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          rw [htdef]
          exact hone
        · exact Filter.Eventually.of_forall fun l => (htpos l).ne'
      have h5 := h3.comp h4
      have h6 : (fun l => (t l)⁻¹ • (F (z + t l • e) - F z))
          = slope (fun s : ℝ => F (z + s • e)) 0 ∘ t := by
        funext l
        simp [slope, Function.comp]
      rw [h6]
      exact h5
    have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (l : ℕ) (z : ℂ) => (t l)⁻¹ • (F (z + t l • e) - F z))
      (f := fun z => fderiv ℝ F z e)
      (bound := Kc.indicator (fun _ => C))
      (fun l => (((hF.continuous.comp (continuous_id.add continuous_const)).sub
        hF.continuous).const_smul (t l)⁻¹).aestronglyMeasurable)
      ((MeasureTheory.integrable_indicator_iff hKcmeas).mpr
        (MeasureTheory.integrableOn_const (s := Kc) (μ := MeasureTheory.volume)
          (hKccomp.measure_lt_top (μ := MeasureTheory.volume)).ne))
      (fun l => Filter.Eventually.of_forall (hdom l))
      (Filter.Eventually.of_forall hlim)
    have h6 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ z, fderiv ℝ F z e)) := by
      simpa only [hzero] using hconv
    exact (tendsto_nhds_unique tendsto_const_nhds h6).symm
  -- STEP 1b: the scaled single-point cutoff factors
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnw : ∀ (ε : ℝ) (c z : ℂ), 0 < ε → ‖ε⁻¹ • (z - c)‖ = ε⁻¹ * ‖z - c‖ := by
    intro ε c z hε
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  have hfacsm : ∀ (ε : ℝ) (c : ℂ), ContDiff ℝ (1 : ℕ) (fun z : ℂ => Θ (ε⁻¹ • (z - c))) :=
    fun ε c => hΘsm.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hfacfd : ∀ (ε : ℝ) (c z : ℂ),
      HasFDerivAt (fun w : ℂ => Θ (ε⁻¹ • (w - c)))
        ((fderiv ℝ Θ (ε⁻¹ • (z - c))).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z := by
    intro ε c z
    have hin : HasFDerivAt (fun w : ℂ => ε⁻¹ • (w - c))
        (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
      ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const c).const_smul (c := ε⁻¹)
    exact (hΘsm.differentiable (by norm_num) (ε⁻¹ • (z - c))).hasFDerivAt.comp z hin
  have hfacap : ∀ (ε : ℝ) (c z : ℂ),
      fderiv ℝ (fun w : ℂ => Θ (ε⁻¹ • (w - c))) z e
        = ε⁻¹ • (fderiv ℝ Θ (ε⁻¹ • (z - c))) e := by
    intro ε c z
    rw [(hfacfd ε c z).fderiv]
    simp
  have hfac0 : ∀ (ε : ℝ) (c z : ℂ), 0 < ε → ‖z - c‖ ≤ ε → Θ (ε⁻¹ • (z - c)) = 0 := by
    intro ε c z hε h
    refine hΘ0 _ ?_
    have h2 : ε⁻¹ * ‖z - c‖ ≤ ε⁻¹ * ε :=
      mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hε))
    rw [inv_mul_cancel₀ hε.ne'] at h2
    rw [hnw ε c z hε]
    exact h2
  have hfac1 : ∀ (ε : ℝ) (c z : ℂ), 0 < ε → Real.sqrt 2 * ε ≤ ‖z - c‖ →
      Θ (ε⁻¹ • (z - c)) = 1 := by
    intro ε c z hε h
    have h1 : Real.sqrt 2 ≤ ε⁻¹ * ‖z - c‖ := by
      have h2 : ε⁻¹ * (Real.sqrt 2 * ε) ≤ ε⁻¹ * ‖z - c‖ :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hε))
      rw [mul_comm (Real.sqrt 2) ε, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at h2
      exact h2
    refine hΘ1 _ ?_
    rw [hnw ε c z hε]
    nlinarith [hr2, hr2pos, h1]
  have hfacd0 : ∀ (ε : ℝ) (c z : ℂ), 0 < ε →
      (‖z - c‖ < ε ∨ Real.sqrt 2 * ε < ‖z - c‖) → fderiv ℝ Θ (ε⁻¹ • (z - c)) = 0 := by
    intro ε c z hε h
    rcases h with h | h
    · refine hdΘ0 _ (Or.inl ?_)
      have h2 : ε⁻¹ * ‖z - c‖ < ε⁻¹ * ε :=
        mul_lt_mul_of_pos_left h (inv_pos.mpr hε)
      rw [inv_mul_cancel₀ hε.ne'] at h2
      have h3 : 0 ≤ ε⁻¹ * ‖z - c‖ :=
        mul_nonneg (le_of_lt (inv_pos.mpr hε)) (norm_nonneg _)
      rw [hnw ε c z hε]
      nlinarith [h2, h3]
    · refine hdΘ0 _ (Or.inr ?_)
      have h2 : ε⁻¹ * (Real.sqrt 2 * ε) < ε⁻¹ * ‖z - c‖ :=
        mul_lt_mul_of_pos_left h (inv_pos.mpr hε)
      rw [mul_comm (Real.sqrt 2) ε, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at h2
      rw [hnw ε c z hε]
      nlinarith [hr2, hr2pos, h2]
  have hfacd : ∀ (ε : ℝ) (c z : ℂ), 0 < ε →
      ‖fderiv ℝ (fun w : ℂ => Θ (ε⁻¹ • (w - c))) z e‖ ≤ B / ε := by
    intro ε c z hε
    rw [hfacap ε c z, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    rw [div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hε))
    calc ‖(fderiv ℝ Θ (ε⁻¹ • (z - c))) e‖
        ≤ ‖fderiv ℝ Θ (ε⁻¹ • (z - c))‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ Θ (ε⁻¹ • (z - c))‖ := by rw [hene, mul_one]
      _ ≤ B := hB _
  -- the test function, its support, and the exceptional points inside it
  intro φ hφ
  obtain ⟨hφsm, hφcs, hφΩ⟩ := hφ
  have hφC1 : ContDiff ℝ (1 : ℕ) φ := hφsm.of_le (by simp)
  set T : Set ℂ := tsupport φ with hTdef
  have hTcomp : IsCompact T := hφcs
  have hTclosed : IsClosed T := isClosed_tsupport φ
  have hφ0 : ∀ z : ℂ, z ∉ T → φ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hdφ0 : ∀ z : ℂ, z ∉ T → fderiv ℝ φ z = 0 := by
    intro z hz
    have hev : φ =ᶠ[nhds z] (fun _ => (0 : ℂ)) :=
      Filter.eventually_of_mem (hTclosed.isOpen_compl.mem_nhds hz) fun w hw => hφ0 w hw
    rw [Filter.EventuallyEq.fderiv_eq hev]
    simp
  obtain ⟨Cφ, hCφ⟩ := hφsm.continuous.bounded_above_of_compact_support hφcs
  have hdφcont : Continuous (fderiv ℝ φ) := (contDiff_one_iff_fderiv.mp hφC1).2
  have hdφcs : HasCompactSupport (fderiv ℝ φ) := HasCompactSupport.fderiv (𝕜 := ℝ) hφcs
  obtain ⟨Cdφ, hCdφ⟩ := hdφcont.bounded_above_of_compact_support hdφcs
  have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 0)
  have hCdφ0 : 0 ≤ Cdφ := le_trans (norm_nonneg _) (hCdφ 0)
  have hfin : (S ∩ T).Finite := hSfin T hφΩ hTcomp
  set P : Finset ℂ := hfin.toFinset with hPdef
  have hPmem : ∀ c : ℂ, c ∈ P ↔ c ∈ S ∧ c ∈ T := by
    intro c
    rw [hPdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hreg : ∀ z : ℂ, z ∈ T → (∀ c ∈ P, z ≠ c) → z ∈ Ω \ S := by
    intro z hzT hz
    exact ⟨hφΩ hzT, fun hzS => hz z ((hPmem z).mpr ⟨hzS, hzT⟩) rfl⟩
  -- STEP 1c: the cutoff family
  set eps : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1) with hepsdef
  have hepspos : ∀ l, 0 < eps l := by
    intro l
    rw [hepsdef]
    positivity
  have heps0 : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    have hone : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [hepsdef]
    exact hone
  set η : ℕ → ℂ → ℝ := fun l z => ∏ c ∈ P, Θ ((eps l)⁻¹ • (z - c)) with hηdef
  have hηsm : ∀ l, ContDiff ℝ (1 : ℕ) (η l) := by
    intro l
    rw [contDiff_iff_contDiffAt]
    intro z
    rw [hηdef]
    exact contDiffAt_prod fun c _ => (hfacsm (eps l) c).contDiffAt
  have hηnn : ∀ (l : ℕ) (z : ℂ), 0 ≤ η l z := by
    intro l z
    rw [hηdef]
    exact Finset.prod_nonneg fun c _ => hΘnn _
  have hηle : ∀ (l : ℕ) (z : ℂ), η l z ≤ 1 := by
    intro l z
    rw [hηdef]
    exact Finset.prod_le_one (fun c _ => hΘnn _) fun c _ => hΘle _
  have hη0 : ∀ (l : ℕ) (z : ℂ), (∃ c ∈ P, ‖z - c‖ ≤ eps l) → η l z = 0 := by
    rintro l z ⟨c, hc, hle⟩
    rw [hηdef]
    exact Finset.prod_eq_zero hc (hfac0 (eps l) c z (hepspos l) hle)
  have hη1 : ∀ (l : ℕ) (z : ℂ), (∀ c ∈ P, Real.sqrt 2 * eps l ≤ ‖z - c‖) → η l z = 1 := by
    intro l z h
    rw [hηdef]
    exact Finset.prod_eq_one fun c hc => hfac1 (eps l) c z (hepspos l) (h c hc)
  have hηfd : ∀ (l : ℕ) (z : ℂ), HasFDerivAt (η l)
      (∑ c ∈ P, (∏ c' ∈ P.erase c, Θ ((eps l)⁻¹ • (z - c'))) •
        fderiv ℝ (fun w : ℂ => Θ ((eps l)⁻¹ • (w - c))) z) z := by
    intro l z
    have h := HasFDerivAt.finsetProd (u := P) (x := z)
      (g := fun (c : ℂ) (w : ℂ) => Θ ((eps l)⁻¹ • (w - c)))
      (g' := fun c => fderiv ℝ (fun w : ℂ => Θ ((eps l)⁻¹ • (w - c))) z)
      (fun c _ => ((hfacsm (eps l) c).differentiable (by norm_num) z).hasFDerivAt)
    simp only [hηdef]
    exact h
  have hdη : ∀ (l : ℕ) (z : ℂ),
      ‖fderiv ℝ (η l) z e‖ ≤ (P.card : ℝ) * (B / eps l) := by
    intro l z
    have hterm : ∀ c ∈ P, ‖((∏ c' ∈ P.erase c, Θ ((eps l)⁻¹ • (z - c'))) •
        fderiv ℝ (fun w : ℂ => Θ ((eps l)⁻¹ • (w - c))) z) e‖ ≤ B / eps l := by
      intro c _
      rw [smul_apply, norm_smul, Real.norm_eq_abs]
      have hp1 : |∏ c' ∈ P.erase c, Θ ((eps l)⁻¹ • (z - c'))| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun c' _ => hΘnn _)]
        exact Finset.prod_le_one (fun c' _ => hΘnn _) fun c' _ => hΘle _
      calc |∏ c' ∈ P.erase c, Θ ((eps l)⁻¹ • (z - c'))| *
            ‖fderiv ℝ (fun w : ℂ => Θ ((eps l)⁻¹ • (w - c))) z e‖
          ≤ 1 * (B / eps l) :=
            mul_le_mul hp1 (hfacd (eps l) c z (hepspos l)) (norm_nonneg _) zero_le_one
        _ = B / eps l := one_mul _
    rw [(hηfd l z).fderiv, sum_apply]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdη0 : ∀ (l : ℕ) (z : ℂ),
      (∀ c ∈ P, ‖z - c‖ < eps l ∨ Real.sqrt 2 * eps l < ‖z - c‖) →
      fderiv ℝ (η l) z e = 0 := by
    intro l z h
    rw [(hηfd l z).fderiv, sum_apply]
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [smul_apply, hfacap (eps l) c z,
      hfacd0 (eps l) c z (hepspos l) (h c hc)]
    simp
  -- the complexified cutoff
  set H : ℕ → ℂ → ℂ := fun l z => ((η l z : ℝ) : ℂ) with hHdef
  have hHsm : ∀ l, ContDiff ℝ (1 : ℕ) (H l) := by
    intro l
    have h : ContDiff ℝ (1 : ℕ) (fun z : ℂ => Complex.ofRealCLM (η l z)) :=
      Complex.ofRealCLM.contDiff.comp (hηsm l)
    simpa [hHdef] using h
  have hHfd : ∀ (l : ℕ) (z : ℂ), HasFDerivAt (H l)
      (Complex.ofRealCLM.comp (fderiv ℝ (η l) z)) z := by
    intro l z
    simp only [hHdef]
    exact Complex.ofRealCLM.hasFDerivAt.comp z
      (((hηsm l).differentiable (by norm_num)) z).hasFDerivAt
  have hHfdap : ∀ (l : ℕ) (z : ℂ), fderiv ℝ (H l) z e = ((fderiv ℝ (η l) z e : ℝ) : ℂ) := by
    intro l z
    rw [(hHfd l z).fderiv]
    simp
  have hHnorm : ∀ (l : ℕ) (z : ℂ), ‖H l z‖ ≤ 1 := by
    intro l z
    simp only [hHdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hηnn l z)]
    exact hηle l z
  have hηnear : ∀ (l : ℕ) (c : ℂ), c ∈ P → ∀ z : ℂ, ‖z - c‖ < eps l →
      η l =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
    intro l c hc z hz
    refine Filter.eventually_of_mem
      (Metric.ball_mem_nhds z (by linarith : (0 : ℝ) < eps l - ‖z - c‖)) ?_
    intro w hw
    refine hη0 l w ⟨c, hc, ?_⟩
    have h1 : ‖w - z‖ < eps l - ‖z - c‖ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h2 : w - c = (w - z) + (z - c) := by ring
    calc ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by rw [h2]; exact norm_add_le _ _
      _ ≤ eps l := by linarith
  -- STEP 2: the product is `C¹` with compact support, so its `j`-th derivative integrates to 0
  set ψ : ℕ → ℂ → ℂ := fun l z => g z * φ z * H l z with hψdef
  have hψzero : ∀ (l : ℕ) (z : ℂ), η l z = 0 → ψ l z = 0 := by
    intro l z h
    simp only [hψdef, hHdef, h]
    simp
  have hψcs : ∀ l, HasCompactSupport (ψ l) := by
    intro l
    refine HasCompactSupport.intro hTcomp ?_
    intro z hz
    simp only [hψdef, hφ0 z hz]
    ring
  have hψnear : ∀ (l : ℕ) (c : ℂ), c ∈ P → ∀ z : ℂ, ‖z - c‖ < eps l →
      ψ l =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    intro l c hc z hz
    filter_upwards [hηnear l c hc z hz] with w hw
    exact hψzero l w hw
  have hψnearT : ∀ (l : ℕ) (z : ℂ), z ∉ T → ψ l =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    intro l z hz
    refine Filter.eventually_of_mem (hTclosed.isOpen_compl.mem_nhds hz) ?_
    intro w hw
    simp only [hψdef, hφ0 w hw]
    ring
  have hψsm : ∀ l, ContDiff ℝ (1 : ℕ) (ψ l) := by
    intro l
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzT : z ∈ T
    · by_cases hzc : ∀ c ∈ P, z ≠ c
      · have hz := hreg z hzT hzc
        simp only [hψdef]
        exact ((hgC1 z hz).mul hφC1.contDiffAt).mul (hHsm l).contDiffAt
      · push Not at hzc
        obtain ⟨c, hc, hzeq⟩ := hzc
        refine contDiffAt_const.congr_of_eventuallyEq (hψnear l c hc z ?_)
        rw [hzeq]
        simpa using hepspos l
    · exact contDiffAt_const.congr_of_eventuallyEq (hψnearT l z hzT)
  have hstep2 : ∀ l, (∫ z, fderiv ℝ (ψ l) z e) = 0 := fun l => ftc (ψ l) (hψsm l) (hψcs l)
  -- STEP 3: the pointwise product rule, valid everywhere
  have hstep3 : ∀ (l : ℕ) (z : ℂ), fderiv ℝ (ψ l) z e
      = v z * (φ z * H l z) + g z * (fderiv ℝ φ z e * H l z)
        + g z * (φ z * fderiv ℝ (H l) z e) := by
    intro l z
    by_cases hzT : z ∈ T
    · by_cases hzc : ∀ c ∈ P, z ≠ c
      · have hz := hreg z hzT hzc
        have hdg : HasFDerivAt g (fderiv ℝ g z) z := (hgdiff z hz).hasFDerivAt
        have hdφ : HasFDerivAt φ (fderiv ℝ φ z) z :=
          (hφC1.differentiable (by norm_num) z).hasFDerivAt
        have hdH : HasFDerivAt (H l) (fderiv ℝ (H l) z) z :=
          ((hHsm l).differentiable (by norm_num) z).hasFDerivAt
        have hgφ : HasFDerivAt (fun w : ℂ => g w * φ w)
            (g z • fderiv ℝ φ z + φ z • fderiv ℝ g z) z := hdg.mul hdφ
        have hfull : HasFDerivAt (ψ l)
            ((g z * φ z) • fderiv ℝ (H l) z +
              (H l z) • (g z • fderiv ℝ φ z + φ z • fderiv ℝ g z)) z := by
          simp only [hψdef]
          exact hgφ.mul hdH
        rw [hfull.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [hgfd z hz]
        ring
      · push Not at hzc
        obtain ⟨c, hc, hzeq⟩ := hzc
        have hcz : ‖z - c‖ < eps l := by rw [hzeq]; simpa using hepspos l
        have h1 : fderiv ℝ (ψ l) z e = 0 := by
          rw [Filter.EventuallyEq.fderiv_eq (hψnear l c hc z hcz)]
          simp
        have h2 : fderiv ℝ (H l) z e = 0 := by
          have hev : H l =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
            filter_upwards [hηnear l c hc z hcz] with w hw
            simp [hHdef, hw]
          rw [Filter.EventuallyEq.fderiv_eq hev]
          simp
        have h3 : H l z = 0 := by
          have := hη0 l z ⟨c, hc, le_of_lt hcz⟩
          simp [hHdef, this]
        rw [h1, h2, h3]
        ring
    · have h1 : fderiv ℝ (ψ l) z e = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (hψnearT l z hzT)]
        simp
      have h2 : φ z = 0 := hφ0 z hzT
      have h3 : fderiv ℝ φ z e = 0 := by rw [hdφ0 z hzT]; simp
      rw [h1, h2, h3]
      ring
  -- integrability of the three terms of (6)
  have hgT : MeasureTheory.Integrable (T.indicator g) MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mp (hgloc T hφΩ hTcomp)
  have hvT : MeasureTheory.Integrable (T.indicator v) MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mp (hvloc T hφΩ hTcomp)
  have hmix : ∀ (u : ℂ → ℂ), MeasureTheory.Integrable (T.indicator u) MeasureTheory.volume →
      ∀ (w : ℂ → ℂ) (Cw : ℝ), Continuous w → (∀ z, ‖w z‖ ≤ Cw) →
      (∀ z, z ∉ T → w z = 0) → MeasureTheory.Integrable (fun z => u z * w z) MeasureTheory.volume := by
    intro u hu w Cw hwc hwb hw0
    have h1 : MeasureTheory.Integrable (fun z => w z * T.indicator u z) MeasureTheory.volume :=
      hu.bdd_mul hwc.aestronglyMeasurable (Filter.Eventually.of_forall hwb)
    refine h1.congr ?_
    filter_upwards with z
    by_cases hz : z ∈ T
    · rw [Set.indicator_of_mem hz]
      ring
    · rw [hw0 z hz]
      ring
  have hdφap : Continuous (fun z : ℂ => fderiv ℝ φ z e) := hdφcont.clm_apply continuous_const
  have hdHap : ∀ l, Continuous (fun z : ℂ => fderiv ℝ (H l) z e) :=
    fun l => (contDiff_one_iff_fderiv.mp (hHsm l)).2.clm_apply continuous_const
  have hint1 : ∀ l, MeasureTheory.Integrable (fun z => v z * (φ z * H l z)) MeasureTheory.volume := by
    intro l
    refine hmix v hvT _ Cφ (hφsm.continuous.mul (hHsm l).continuous) (fun z => ?_) ?_
    · calc ‖φ z * H l z‖ = ‖φ z‖ * ‖H l z‖ := norm_mul _ _
        _ ≤ Cφ * 1 := mul_le_mul (hCφ z) (hHnorm l z) (norm_nonneg _) hCφ0
        _ = Cφ := mul_one _
    · intro z hz
      rw [hφ0 z hz]
      ring
  have hint2 : ∀ l, MeasureTheory.Integrable (fun z => g z * (fderiv ℝ φ z e * H l z)) MeasureTheory.volume := by
    intro l
    refine hmix g hgT _ Cdφ (hdφap.mul (hHsm l).continuous) (fun z => ?_) ?_
    · calc ‖fderiv ℝ φ z e * H l z‖ = ‖fderiv ℝ φ z e‖ * ‖H l z‖ := norm_mul _ _
        _ ≤ Cdφ * 1 := by
            refine mul_le_mul ?_ (hHnorm l z) (norm_nonneg _) hCdφ0
            calc ‖fderiv ℝ φ z e‖ ≤ ‖fderiv ℝ φ z‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
              _ = ‖fderiv ℝ φ z‖ := by rw [hene, mul_one]
              _ ≤ Cdφ := hCdφ z
        _ = Cdφ := mul_one _
    · intro z hz
      rw [hdφ0 z hz]
      simp
  have hint3 : ∀ l, MeasureTheory.Integrable (fun z => g z * (φ z * fderiv ℝ (H l) z e)) MeasureTheory.volume := by
    intro l
    refine hmix g hgT _ (Cφ * ((P.card : ℝ) * (B / eps l)))
      (hφsm.continuous.mul (hdHap l)) (fun z => ?_) ?_
    · have h1 : ‖fderiv ℝ (H l) z e‖ ≤ (P.card : ℝ) * (B / eps l) := by
        rw [hHfdap l z, Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact hdη l z
      calc ‖φ z * fderiv ℝ (H l) z e‖ = ‖φ z‖ * ‖fderiv ℝ (H l) z e‖ := norm_mul _ _
        _ ≤ Cφ * ((P.card : ℝ) * (B / eps l)) :=
            mul_le_mul (hCφ z) h1 (norm_nonneg _) hCφ0
    · intro z hz
      rw [hφ0 z hz]
      ring
  -- the identity (6)
  have hsix : ∀ l, (∫ z, v z * (φ z * H l z)) + (∫ z, g z * (fderiv ℝ φ z e * H l z))
      + (∫ z, g z * (φ z * fderiv ℝ (H l) z e)) = 0 := by
    intro l
    have h0 : (∫ z, fderiv ℝ (ψ l) z e) = 0 := hstep2 l
    have h12 : MeasureTheory.Integrable (fun z => v z * (φ z * H l z)
        + g z * (fderiv ℝ φ z e * H l z)) MeasureTheory.volume := (hint1 l).add (hint2 l)
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hstep3 l)),
      MeasureTheory.integral_add h12 (hint3 l), MeasureTheory.integral_add (hint1 l) (hint2 l)] at h0
    exact h0
  -- STEP 4: the first two terms converge
  have hPnull : ∀ᵐ z : ℂ, z ∉ (P : Set ℂ) := by
    have h := P.finite_toSet.measure_zero (MeasureTheory.volume : MeasureTheory.Measure ℂ)
    rw [← MeasureTheory.compl_mem_ae_iff] at h
    exact h
  have hHlim : ∀ z : ℂ, z ∉ (P : Set ℂ) →
      Filter.Tendsto (fun l => H l z) Filter.atTop (nhds 1) := by
    intro z hz
    have hd : ∀ c ∈ P, 0 < ‖z - c‖ := by
      intro c hc
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact hz (by rw [h]; exact_mod_cast hc)
    have hall : ∀ᶠ l in Filter.atTop, ∀ c ∈ P, Real.sqrt 2 * eps l ≤ ‖z - c‖ := by
      rw [Filter.eventually_all_finset]
      intro c hc
      have h1 : Filter.Tendsto (fun l => Real.sqrt 2 * eps l) Filter.atTop (nhds 0) := by
        simpa using heps0.const_mul (Real.sqrt 2)
      exact (h1.eventually (gt_mem_nhds (hd c hc))).mono fun l h => le_of_lt h
    have hev : (fun l => H l z) =ᶠ[Filter.atTop] (fun _ => (1 : ℂ)) := by
      filter_upwards [hall] with l hl
      simp [hHdef, hη1 l z hl]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hlim1 : Filter.Tendsto (fun l => ∫ z, v z * (φ z * H l z)) Filter.atTop
      (nhds (∫ z, v z * φ z)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => Cφ * ‖T.indicator v z‖)
      (fun l => (hint1 l).aestronglyMeasurable)
      (hvT.norm.const_mul Cφ) (fun l => Filter.Eventually.of_forall fun z => ?_) ?_
    · by_cases hz : z ∈ T
      · rw [Set.indicator_of_mem hz, norm_mul, norm_mul, mul_comm Cφ ‖v z‖]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖φ z‖ * ‖H l z‖ ≤ Cφ * 1 := mul_le_mul (hCφ z) (hHnorm l z) (norm_nonneg _) hCφ0
          _ = Cφ := mul_one _
      · rw [hφ0 z hz]
        simp
        positivity
    · filter_upwards [hPnull] with z hz
      have h := (hHlim z hz).const_mul (v z * φ z)
      simpa [mul_assoc] using h
  have hlim2 : Filter.Tendsto (fun l => ∫ z, g z * (fderiv ℝ φ z e * H l z)) Filter.atTop
      (nhds (∫ z, g z * fderiv ℝ φ z e)) := by
    have hdφb : ∀ z : ℂ, ‖fderiv ℝ φ z e‖ ≤ Cdφ := by
      intro z
      calc ‖fderiv ℝ φ z e‖ ≤ ‖fderiv ℝ φ z‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ φ z‖ := by rw [hene, mul_one]
        _ ≤ Cdφ := hCdφ z
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun z => Cdφ * ‖T.indicator g z‖)
      (fun l => (hint2 l).aestronglyMeasurable)
      (hgT.norm.const_mul Cdφ) (fun l => Filter.Eventually.of_forall fun z => ?_) ?_
    · by_cases hz : z ∈ T
      · rw [Set.indicator_of_mem hz, norm_mul, norm_mul, mul_comm Cdφ ‖g z‖]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖fderiv ℝ φ z e‖ * ‖H l z‖ ≤ Cdφ * 1 :=
              mul_le_mul (hdφb z) (hHnorm l z) (norm_nonneg _) hCdφ0
          _ = Cdφ := mul_one _
      · rw [hdφ0 z hz]
        simp
        positivity
    · filter_upwards [hPnull] with z hz
      have h := (hHlim z hz).const_mul (g z * fderiv ℝ φ z e)
      simpa [mul_assoc] using h
  -- STEP 5: the cutoff term vanishes; this is where `β < 1` is used
  have hgrowall : ∀ c : ℂ, ∃ Mρ : ℝ × ℝ, 0 < Mρ.2 ∧ 0 ≤ Mρ.1 ∧
      (c ∈ P → ∀ z : ℂ, 0 < ‖z - c‖ → ‖z - c‖ < Mρ.2 →
        ‖g z‖ ≤ Mρ.1 * ‖z - c‖ ^ (-β)) := by
    intro c
    by_cases hc : c ∈ P
    · obtain ⟨M, ρ, hρ, hbd⟩ := hgrow c ((hPmem c).mp hc).1
      refine ⟨(max M 0, ρ), hρ, le_max_right _ _, fun _ z h1 h2 => ?_⟩
      exact le_trans (hbd z h1 h2)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact ⟨(0, 1), one_pos, le_rfl, fun h => absurd h hc⟩
  choose Mρ hρpos hMnn hbnd using hgrowall
  set Msum : ℝ := ∑ c ∈ P, (Mρ c).1 with hMsumdef
  have hMsum0 : 0 ≤ Msum := Finset.sum_nonneg fun c _ => hMnn c
  have hMle : ∀ c ∈ P, (Mρ c).1 ≤ Msum :=
    fun c hc => Finset.single_le_sum (fun c' _ => hMnn c') hc
  set Ann : ℂ → ℕ → Set ℂ :=
    fun c l => {z : ℂ | eps l ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ Real.sqrt 2 * eps l} with hAnndef
  have hAnnmem : ∀ (c : ℂ) (l : ℕ) (z : ℂ),
      z ∈ Ann c l ↔ (eps l ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ Real.sqrt 2 * eps l) := by
    intro c l z
    rw [hAnndef]
    exact Iff.rfl
  have hAnnclosed : ∀ (c : ℂ) (l : ℕ), IsClosed (Ann c l) := by
    intro c l
    have hcont : Continuous (fun z : ℂ => ‖z - c‖) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have h1 : IsClosed {z : ℂ | eps l ≤ ‖z - c‖} := isClosed_le continuous_const hcont
    have h2 : IsClosed {z : ℂ | ‖z - c‖ ≤ Real.sqrt 2 * eps l} :=
      isClosed_le hcont continuous_const
    have h3 : Ann c l
        = {z : ℂ | eps l ≤ ‖z - c‖} ∩ {z : ℂ | ‖z - c‖ ≤ Real.sqrt 2 * eps l} := by
      rw [hAnndef]
      rfl
    rw [h3]
    exact h1.inter h2
  set AU : ℕ → Set ℂ := fun l => ⋃ c ∈ P, Ann c l with hAUdef
  have hAUmeas : ∀ l, MeasurableSet (AU l) := by
    intro l
    rw [hAUdef]
    exact Finset.measurableSet_biUnion _ fun c _ => (hAnnclosed c l).measurableSet
  have hballvol : ∀ (c : ℂ) (l : ℕ),
      MeasureTheory.volume (Ann c l) ≤ ENNReal.ofReal (2 * Real.pi * eps l ^ 2) := by
    intro c l
    have h1 : Ann c l ⊆ Metric.closedBall c (Real.sqrt 2 * eps l) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact ((hAnnmem c l z).mp hz).2
    refine le_trans (MeasureTheory.measure_mono h1) (le_of_eq ?_)
    have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [Complex.volume_closedBall, hpi, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, hr2]
    ring
  have hAUle : ∀ l, MeasureTheory.volume (AU l)
      ≤ (P.card : ENNReal) * ENNReal.ofReal (2 * Real.pi * eps l ^ 2) := by
    intro l
    rw [hAUdef]
    refine le_trans (MeasureTheory.measure_biUnion_finset_le P fun c => Ann c l) ?_
    refine le_trans (Finset.sum_le_sum fun c _ => hballvol c l) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hAUtop : ∀ l, ((P.card : ENNReal) * ENNReal.ofReal (2 * Real.pi * eps l ^ 2)) ≠ ⊤ :=
    fun l => ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hAUfin : ∀ l, MeasureTheory.volume (AU l) ≠ ⊤ := fun l =>
    (lt_of_le_of_lt (hAUle l) (lt_top_iff_ne_top.mpr (hAUtop l))).ne
  have hAUvolR : ∀ l, (MeasureTheory.volume (AU l)).toReal ≤ (P.card : ℝ) * (2 * Real.pi * eps l ^ 2) := by
    intro l
    refine le_trans (ENNReal.toReal_mono (hAUtop l) (hAUle l)) (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_natCast]
  set KL : ℕ → ℝ := fun l => Cφ * ((P.card : ℝ) * (B / eps l)) with hKLdef
  have hKL0 : ∀ l, 0 ≤ KL l := by
    intro l
    rw [hKLdef]
    exact mul_nonneg hCφ0 (mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg hB0 (hepspos l).le))
  have hwbnd : ∀ (l : ℕ) (z : ℂ), ‖φ z * fderiv ℝ (H l) z e‖ ≤ KL l := by
    intro l z
    rw [norm_mul, hKLdef]
    refine mul_le_mul (hCφ z) ?_ (norm_nonneg _) hCφ0
    rw [hHfdap l z, Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact hdη l z
  have hptw : ∀ l : ℕ, (∀ c ∈ P, Real.sqrt 2 * eps l < (Mρ c).2) →
      ∀ z : ℂ, ‖g z * (φ z * fderiv ℝ (H l) z e)‖
        ≤ (AU l).indicator (fun _ => KL l * (Msum * eps l ^ (-β))) z := by
    intro l hρl z
    by_cases hz : z ∈ AU l
    · rw [Set.indicator_of_mem hz]
      obtain ⟨c, hc, hzc⟩ : ∃ c ∈ P, z ∈ Ann c l := by
        rw [hAUdef] at hz
        simpa using hz
      rw [hAnnmem] at hzc
      have hzc0 : 0 < ‖z - c‖ := lt_of_lt_of_le (hepspos l) hzc.1
      have hzcρ : ‖z - c‖ < (Mρ c).2 := lt_of_le_of_lt hzc.2 (hρl c hc)
      have hrp : ‖z - c‖ ^ (-β) ≤ eps l ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (hepspos l) hzc.1 (by linarith)
      have hg2 : ‖g z‖ ≤ Msum * eps l ^ (-β) :=
        le_trans (hbnd c hc z hzc0 hzcρ)
          (mul_le_mul (hMle c hc) hrp (Real.rpow_nonneg (norm_nonneg _) _) hMsum0)
      rw [norm_mul]
      calc ‖g z‖ * ‖φ z * fderiv ℝ (H l) z e‖
          ≤ (Msum * eps l ^ (-β)) * KL l :=
            mul_le_mul hg2 (hwbnd l z) (norm_nonneg _)
              (mul_nonneg hMsum0 (Real.rpow_nonneg (hepspos l).le _))
        _ = KL l * (Msum * eps l ^ (-β)) := by ring
    · rw [Set.indicator_of_notMem hz]
      have h0 : fderiv ℝ (η l) z e = 0 := by
        refine hdη0 l z fun c hc => ?_
        by_contra hcon
        push Not at hcon
        refine absurd ?_ hz
        rw [hAUdef]
        simp only [Set.mem_iUnion]
        exact ⟨c, hc, (hAnnmem c l z).mpr ⟨hcon.1, hcon.2⟩⟩
      rw [hHfdap l z, h0]
      simp
  have hbndint : ∀ l,
      MeasureTheory.Integrable ((AU l).indicator (fun _ => KL l * (Msum * eps l ^ (-β)))) MeasureTheory.volume :=
    fun l => (MeasureTheory.integrable_indicator_iff (hAUmeas l)).mpr (MeasureTheory.integrableOn_const (hAUfin l))
  have hnormbnd : ∀ l : ℕ, (∀ c ∈ P, Real.sqrt 2 * eps l < (Mρ c).2) →
      ‖∫ z, g z * (φ z * fderiv ℝ (H l) z e)‖
        ≤ (P.card : ℝ) * (2 * Real.pi * eps l ^ 2) * (KL l * (Msum * eps l ^ (-β))) := by
    intro l hρl
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have h1 : (∫ z, ‖g z * (φ z * fderiv ℝ (H l) z e)‖)
        ≤ ∫ z, (AU l).indicator (fun _ => KL l * (Msum * eps l ^ (-β))) z :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
        (hbndint l) (Filter.Eventually.of_forall (hptw l hρl))
    have h2 : (∫ z, (AU l).indicator (fun _ => KL l * (Msum * eps l ^ (-β))) z)
        = (MeasureTheory.volume (AU l)).toReal * (KL l * (Msum * eps l ^ (-β))) := by
      rw [MeasureTheory.integral_indicator (hAUmeas l), MeasureTheory.setIntegral_const, smul_eq_mul]
      rfl
    rw [h2] at h1
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_right (hAUvolR l)
      (mul_nonneg (hKL0 l) (mul_nonneg hMsum0 (Real.rpow_nonneg (hepspos l).le _)))
  set D : ℝ := (P.card : ℝ) ^ 2 * (2 * Real.pi) * Cφ * B * Msum with hDdef
  have halg : ∀ x y n : ℝ, x ≠ 0 →
      n * (2 * Real.pi * x ^ 2) * (Cφ * (n * (B / x)) * (Msum * y))
        = n ^ 2 * (2 * Real.pi) * Cφ * B * Msum * (x * y) := by
    intro x y n hx
    field_simp
  have hDl : ∀ l : ℕ,
      (P.card : ℝ) * (2 * Real.pi * eps l ^ 2) * (KL l * (Msum * eps l ^ (-β)))
        = D * eps l ^ (1 - β) := by
    intro l
    have hsplit : (eps l : ℝ) ^ (1 - β) = eps l * eps l ^ (-β) := by
      rw [show (1 - β) = 1 + (-β) by ring, Real.rpow_add (hepspos l), Real.rpow_one]
    rw [hsplit]
    simp only [hKLdef, hDdef]
    exact halg (eps l) (eps l ^ (-β)) (P.card : ℝ) (hepspos l).ne'
  have hDtend : Filter.Tendsto (fun l => D * eps l ^ (1 - β)) Filter.atTop (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (1 - β)) 0 :=
      Real.continuousAt_rpow_const 0 (1 - β) (Or.inr (by linarith))
    have h2 : Filter.Tendsto (fun l => eps l ^ (1 - β)) Filter.atTop
        (nhds ((0 : ℝ) ^ (1 - β))) := hc.tendsto.comp heps0
    rw [Real.zero_rpow (by linarith : (1 : ℝ) - β ≠ 0)] at h2
    simpa using h2.const_mul D
  have hlim3 : Filter.Tendsto (fun l => ∫ z, g z * (φ z * fderiv ℝ (H l) z e))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hDtend
    have hev : ∀ᶠ l in Filter.atTop, ∀ c ∈ P, Real.sqrt 2 * eps l < (Mρ c).2 := by
      rw [Filter.eventually_all_finset]
      intro c hc
      have h1 : Filter.Tendsto (fun l => Real.sqrt 2 * eps l) Filter.atTop (nhds 0) := by
        simpa using heps0.const_mul (Real.sqrt 2)
      exact h1.eventually (gt_mem_nhds (hρpos c))
    filter_upwards [hev] with l hl
    rw [← hDl l]
    exact hnormbnd l hl
  -- STEP 6: pass to the limit in (6)
  have hsum : (∫ z, v z * φ z) + (∫ z, g z * fderiv ℝ φ z e) + 0 = 0 := by
    have h := (hlim1.add hlim2).add hlim3
    have h0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds ((∫ z, v z * φ z) + (∫ z, g z * fderiv ℝ φ z e) + 0)) := by
      simpa only [hsix] using h
    exact (tendsto_nhds_unique tendsto_const_nhds h0).symm
  have hgoal : (∫ z, g z * fderiv ℝ φ z e) = -∫ z, v z * φ z := by linear_combination hsum
  exact hgoal
