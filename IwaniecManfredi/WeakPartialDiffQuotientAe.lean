import IwaniecManfredi.WeakPartialLineIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option maxHeartbeats 1000000

open MeasureTheory

/-- The difference quotients of a locally integrable function whose
distributional `j`-th partial derivative `D` is locally integrable converge to
`D` almost everywhere on each compact subset, along a suitable sequence of
increments tending to `0`.

The `L^1(K)` convergence of the difference quotients is what the translation
continuity of `L^1` buys from the line-integral identity; a sequence of
increments realising almost-everywhere convergence is then extracted from it.
A full (not merely subsequential) almost-everywhere statement is false in
general -- the exceptional set depends on the increment -- and is not needed:
what the paper's use requires is one null sequence of increments along which
the quotients converge pointwise almost everywhere, which is exactly what
lets the distributional derivative be identified with a classical one
wherever the latter exists. -/
theorem WeakPartialDiffQuotientAe (Ω : Set ℂ) (hΩ : IsOpen Ω) (j : Fin 2) (u D : ℂ → ℂ)
    (hu : MemLpLocOn 1 Ω u) (hD : MemLpLocOn 1 Ω D)
    (hweak : IsWeakPartialOn Ω j u D)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ t : ℕ → ℝ, (∀ l, t l ≠ 0) ∧ Filter.Tendsto t Filter.atTop (nhds 0) ∧
      ∀ᵐ z : ℂ, z ∈ K →
        Filter.Tendsto
          (fun l => (t l)⁻¹ • (u (z + t l • (if j = 0 then 1 else Complex.I)) - u z))
          Filter.atTop (nhds (D z)) := by
  -- STEP 0: the collar and the truncation
  obtain ⟨δ₁, hδ₁, hδ₁Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨δ₂, hδ₂, hline⟩ := WeakPartialLineIntegral Ω hΩ j u D hu hD hweak K hK hKΩ
  set e : ℂ := if j = 0 then 1 else Complex.I with hedef
  have hene : ‖e‖ = 1 := by rw [hedef]; split <;> simp
  set W : Set ℂ := Metric.cthickening δ₁ K with hWdef
  have hWcomp : IsCompact W := hK.cthickening
  have hKW : K ⊆ W := Metric.self_subset_cthickening K
  set V : ℂ → ℂ := W.indicator D with hVdef
  have hV : Integrable V volume := by
    rw [hVdef]; exact memLp_one_iff_integrable.mp (hD W hδ₁Ω hWcomp)
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  have hseg : ∀ z ∈ K, ∀ s : ℝ, |s| ≤ δ → z + s • e ∈ W := by
    intro z hz s hs
    refine Metric.mem_cthickening_of_dist_le _ z δ₁ K hz ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hene, Real.norm_eq_abs, mul_one]
    exact le_trans hs (min_le_left _ _)
  -- TRANSLATION CONTINUITY IN L¹, by density of the compactly supported continuous functions
  have htrans : ∀ η : ℝ, 0 < η → ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε →
      (∫ x, ‖V (x + s • e) - V x‖) ≤ η := by
    intro η hη
    obtain ⟨h, hhsupp, hhle, hhcont, hhint⟩ :=
      hV.exists_hasCompactSupport_integral_sub_le (show (0 : ℝ) < η / 3 by linarith)
    obtain ⟨C, hC⟩ := hhsupp.exists_bound_of_continuous hhcont
    obtain ⟨R, hR⟩ := hhsupp.isCompact.isBounded.subset_closedBall (0 : ℂ)
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    -- `s ↦ ∫ ‖h(· + s e) - h‖` is continuous at `0`, by dominated convergence
    have hcont0 : ContinuousAt (fun s : ℝ => ∫ x, ‖h (x + s • e) - h x‖) 0 := by
      refine continuousAt_of_dominated (bound :=
        (Metric.closedBall (0 : ℂ) (1 + R)).indicator (fun _ => 2 * C + 1)) ?_ ?_ ?_ ?_
      · filter_upwards with s
        exact (((hhcont.comp (by fun_prop)).sub hhcont).norm).aestronglyMeasurable
      · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        by_cases hx : x ∈ Metric.closedBall (0 : ℂ) (1 + R)
        · rw [Set.indicator_of_mem hx]
          have := hC (x + s • e); have := hC x
          calc ‖h (x + s • e) - h x‖ ≤ ‖h (x + s • e)‖ + ‖h x‖ := norm_sub_le _ _
            _ ≤ 2 * C + 1 := by linarith [hC (x + s • e), hC x]
        · rw [Set.indicator_of_notMem hx]
          have hxz : h x = 0 := by
            by_contra hne
            exact hx (Metric.closedBall_subset_closedBall (by linarith : R ≤ 1 + R)
              (hR (subset_tsupport h hne)))
          have hxs : h (x + s • e) = 0 := by
            by_contra hne
            have hmem : x + s • e ∈ Metric.closedBall (0 : ℂ) R := hR (subset_tsupport h hne)
            simp only [Metric.mem_closedBall, dist_zero_right] at hmem hx ⊢
            have hsn : ‖s • e‖ ≤ 1 := by
              rw [norm_smul, hene, Real.norm_eq_abs, mul_one]
              have hb := Metric.mem_ball.mp hs
              rw [Real.dist_eq, sub_zero] at hb
              exact hb.le
            refine hx ?_
            calc ‖x‖ = ‖(x + s • e) - s • e‖ := by ring_nf
              _ ≤ ‖x + s • e‖ + ‖s • e‖ := norm_sub_le _ _
              _ ≤ R + 1 := by linarith
              _ = 1 + R := by ring
          rw [hxs, hxz]
          simp
      · rw [integrable_indicator_iff measurableSet_closedBall]
        exact integrableOn_const (Metric.isBounded_closedBall.measure_lt_top).ne (by simp)
      · filter_upwards with x
        exact ((hhcont.comp (by fun_prop)).sub continuous_const).norm.continuousAt
    have hval0 : (∫ x, ‖h (x + (0 : ℝ) • e) - h x‖) = 0 := by simp
    have hseq : Filter.Tendsto (fun s : ℝ => ∫ x, ‖h (x + s • e) - h x‖) (nhds 0) (nhds 0) := by
      have h0 := hcont0
      rw [ContinuousAt, hval0] at h0
      exact h0
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hseq.eventually (gt_mem_nhds (show (0 : ℝ) < η / 3 by linarith)))
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hsd : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]
      calc |s| ≤ ε / 2 := hs
        _ < ε := by linarith
    have hmid : (∫ x, ‖h (x + s • e) - h x‖) < η / 3 := hball hsd
    have hVt : Integrable (fun x => V (x + s • e)) volume := hV.comp_add_right (s • e)
    have hht : Integrable (fun x => h (x + s • e)) volume := hhint.comp_add_right (s • e)
    have hA1 : Integrable (fun x => ‖V (x + s • e) - h (x + s • e)‖) volume := (hVt.sub hht).norm
    have hA2 : Integrable (fun x => ‖h (x + s • e) - h x‖) volume := (hht.sub hhint).norm
    have hA3 : Integrable (fun x => ‖h x - V x‖) volume := (hhint.sub hV).norm
    have hA12 : Integrable (fun x => ‖V (x + s • e) - h (x + s • e)‖
        + ‖h (x + s • e) - h x‖) volume := hA1.add hA2
    have hsum : Integrable (fun x => (‖V (x + s • e) - h (x + s • e)‖
        + ‖h (x + s • e) - h x‖) + ‖h x - V x‖) volume := hA12.add hA3
    have hptw : ∀ x : ℂ, ‖V (x + s • e) - V x‖
        ≤ (‖V (x + s • e) - h (x + s • e)‖ + ‖h (x + s • e) - h x‖) + ‖h x - V x‖ := by
      intro x
      have hre : V (x + s • e) - V x
          = (V (x + s • e) - h (x + s • e)) + ((h (x + s • e) - h x) + (h x - V x)) := by ring
      calc ‖V (x + s • e) - V x‖ = ‖(V (x + s • e) - h (x + s • e))
              + ((h (x + s • e) - h x) + (h x - V x))‖ := by rw [hre]
        _ ≤ ‖V (x + s • e) - h (x + s • e)‖ + ‖(h (x + s • e) - h x) + (h x - V x)‖ :=
            norm_add_le _ _
        _ ≤ ‖V (x + s • e) - h (x + s • e)‖ + (‖h (x + s • e) - h x‖ + ‖h x - V x‖) := by
            linarith [norm_add_le (h (x + s • e) - h x) (h x - V x)]
        _ = (‖V (x + s • e) - h (x + s • e)‖ + ‖h (x + s • e) - h x‖) + ‖h x - V x‖ := by ring
    have he1 : (∫ x, ‖V (x + s • e) - h (x + s • e)‖) = ∫ x, ‖V x - h x‖ :=
      integral_add_right_eq_self (fun x => ‖V x - h x‖) (s • e)
    have he3 : (∫ x, ‖h x - V x‖) = ∫ x, ‖V x - h x‖ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => norm_sub_rev _ _)
    calc (∫ x, ‖V (x + s • e) - V x‖)
        ≤ ∫ x, ((‖V (x + s • e) - h (x + s • e)‖ + ‖h (x + s • e) - h x‖) + ‖h x - V x‖) :=
          integral_mono ((hVt.sub hV).norm) hsum hptw
      _ = ((∫ x, ‖V (x + s • e) - h (x + s • e)‖) + ∫ x, ‖h (x + s • e) - h x‖)
            + ∫ x, ‖h x - V x‖ := by
          rw [integral_add hA12 hA3, integral_add hA1 hA2]
      _ ≤ η := by rw [he1, he3]; linarith
  -- the shear `(s, z) ↦ (s, z + s • e)` preserves `volume ×ˢ volume` on `ℝ × ℂ`
  have hshear : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 + p.1 • e))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product (by fun_prop)
      (Filter.Eventually.of_forall fun s => map_add_right_eq_self volume (s • e))
  have hprodAE : ∀ (t : ℝ) (G : ℂ → ℂ), AEMeasurable G volume →
      AEMeasurable (fun p : ℂ × ℝ => G (p.1 + p.2 • e))
        (volume.prod (volume.restrict (Set.uIoc 0 t))) := by
    intro t G hG
    have h1 : AEMeasurable (fun q : ℝ × ℂ => G q.2) (volume.prod volume) :=
      hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEMeasurable (fun q : ℝ × ℂ => G (q.2 + q.1 • e)) (volume.prod volume) :=
      h1.comp_quasiMeasurePreserving hshear.quasiMeasurePreserving
    have h2' : AEMeasurable (fun q : ℝ × ℂ => G (q.2 + q.1 • e))
        ((volume.restrict (Set.uIoc 0 t)).prod volume) := by
      have hr : (volume.restrict (Set.uIoc 0 t)).prod (volume : Measure ℂ)
          = (volume.prod volume).restrict (Set.uIoc 0 t ×ˢ (Set.univ : Set ℂ)) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hr]; exact h2.restrict
    exact h2'.comp_quasiMeasurePreserving
      (Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
        (ν := (volume : Measure ℝ).restrict (Set.uIoc 0 t))).quasiMeasurePreserving
  have hfstAE : ∀ (t : ℝ) (G : ℂ → ℂ), AEMeasurable G volume →
      AEMeasurable (fun p : ℂ × ℝ => G p.1)
        (volume.prod (volume.restrict (Set.uIoc 0 t))) := fun t G hG =>
    hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hvolI : ∀ t : ℝ, volume (Set.uIoc 0 t) = ENNReal.ofReal |t| := by
    intro t
    rw [Set.uIoc, Real.volume_Ioc]
    congr 1
    by_cases hposv : (0 : ℝ) ≤ t
    · rw [max_eq_right hposv, min_eq_left hposv, abs_of_nonneg hposv]; ring
    · replace hposv : t < 0 := not_le.mp hposv
      rw [max_eq_left hposv.le, min_eq_right hposv.le, abs_of_neg hposv]; ring
  -- the plain Tonelli bound, used for the segment integrability
  have hton : ∀ (t : ℝ) (G : ℂ → ℂ), AEMeasurable G volume →
      (∫⁻ z, ∫⁻ s in Set.uIoc 0 t, ‖G (z + s • e)‖ₑ)
        ≤ (∫⁻ x, ‖G x‖ₑ) * volume (Set.uIoc 0 t) := by
    intro t G hG
    rw [lintegral_lintegral_swap (hprodAE t G hG).enorm]
    calc (∫⁻ s in Set.uIoc 0 t, ∫⁻ z, ‖G (z + s • e)‖ₑ)
        = ∫⁻ _ in Set.uIoc 0 t, ∫⁻ x, ‖G x‖ₑ := by
          refine setLIntegral_congr_fun measurableSet_uIoc (fun s _ => ?_)
          exact lintegral_add_right_eq_self (fun x => ‖G x‖ₑ) (s • e)
      _ = (∫⁻ x, ‖G x‖ₑ) * volume (Set.uIoc 0 t) := setLIntegral_const _ _
      _ ≤ (∫⁻ x, ‖G x‖ₑ) * volume (Set.uIoc 0 t) := le_rfl
  -- a.e. integrability of the segment integrand (the verifier's note (ii))
  have hVsegint : ∀ t : ℝ, ∀ᵐ z : ℂ,
      Integrable (fun s : ℝ => V (z + s • e)) (volume.restrict (Set.uIoc 0 t)) := by
    intro t
    refine Integrable.prod_right_ae (f := fun p : ℂ × ℝ => V (p.1 + p.2 • e)) ?_
    refine ⟨aestronglyMeasurable_iff_aemeasurable.mpr (hprodAE t V hV.aemeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hsw : (∫⁻ p : ℂ × ℝ, ‖V (p.1 + p.2 • e)‖ₑ
          ∂(volume.prod (volume.restrict (Set.uIoc 0 t))))
        = ∫⁻ z, ∫⁻ s in Set.uIoc 0 t, ‖V (z + s • e)‖ₑ :=
      lintegral_prod _ (hprodAE t V hV.aemeasurable).enorm
    rw [hsw]
    refine lt_of_le_of_lt (hton t V hV.aemeasurable) (ENNReal.mul_lt_top ?_ ?_)
    · rw [← hasFiniteIntegral_iff_enorm]; exact hV.2
    · rw [hvolI]; exact ENNReal.ofReal_lt_top
  -- `|s| ≤ |t|` on the interval between `0` and `t`
  have huIcc : ∀ t s : ℝ, s ∈ Set.uIcc (0 : ℝ) t → |s| ≤ |t| := by
    intro t s hs
    rcases Set.mem_uIcc.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [abs_of_nonneg ha]; exact le_trans hb (le_abs_self t)
    · rw [abs_of_nonpos hb]; exact le_trans (neg_le_neg ha) (neg_le_abs t)
  have huIoc : ∀ t s : ℝ, s ∈ Set.uIoc (0 : ℝ) t → |s| ≤ |t| :=
    fun t s hs => huIcc t s (Set.uIoc_subset_uIcc hs)
  -- STEP 3: the difference quotients converge in `L¹(K)`
  have hstep3 : ∀ η : ℝ, 0 < η → ∃ δ' > 0, δ' ≤ δ ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ δ' →
      (∫⁻ z in K, ‖t⁻¹ • (u (z + t • e) - u z) - D z‖ₑ) ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨ε, hε, hεle⟩ := htrans η hη
    refine ⟨min δ ε, lt_min hδpos hε, min_le_left _ _, fun t ht0 htle => ?_⟩
    have htδ : |t| ≤ δ := le_trans htle (min_le_left _ _)
    have htε : |t| ≤ ε := le_trans htle (min_le_right _ _)
    have hptw : ∀ᵐ z : ℂ ∂(volume.restrict K),
        ‖t⁻¹ • (u (z + t • e) - u z) - D z‖ₑ
          ≤ ENNReal.ofReal |t|⁻¹ * ∫⁻ s in Set.uIoc 0 t, ‖V (z + s • e) - V z‖ₑ := by
      rw [ae_restrict_iff' hK.measurableSet]
      filter_upwards [hline t (le_trans htδ (min_le_right _ _)), hVsegint t] with
        z hz hzint hzK
      have hDV : ∀ s ∈ Set.uIcc (0 : ℝ) t, D (z + s • e) = V (z + s • e) := by
        intro s hs
        rw [hVdef, Set.indicator_of_mem (hseg z hzK s (le_trans (huIcc t s hs) htδ))]
      have hzid2 : u (z + t • e) - u z = ∫ s in (0 : ℝ)..t, V (z + s • e) := by
        rw [hz hzK]; exact intervalIntegral.integral_congr hDV
      have hDz : D z = V z := by rw [hVdef, Set.indicator_of_mem (hKW hzK)]
      have hconst : (∫ _s in (0 : ℝ)..t, V z) = t • V z := by
        rw [intervalIntegral.integral_const]; simp
      have hsplit : (∫ s in (0 : ℝ)..t, V (z + s • e)) - (∫ _s in (0 : ℝ)..t, V z)
          = ∫ s in (0 : ℝ)..t, (V (z + s • e) - V z) :=
        (intervalIntegral.integral_sub
          (by rw [intervalIntegrable_iff]; exact hzint) intervalIntegrable_const).symm
      have hkey : t⁻¹ • (u (z + t • e) - u z) - D z
          = t⁻¹ • ∫ s in (0 : ℝ)..t, (V (z + s • e) - V z) := by
        rw [hzid2, hDz, ← hsplit, hconst, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [hkey, enorm_smul]
      have hnorm : ‖t⁻¹‖ₑ = ENNReal.ofReal |t|⁻¹ := by
        rw [Real.enorm_eq_ofReal_abs, abs_inv]
      rw [hnorm]
      refine mul_le_mul' le_rfl ?_
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, enorm_smul]
      have hone : ‖(if (0 : ℝ) ≤ t then (1 : ℝ) else -1)‖ₑ = 1 := by split <;> simp
      rw [hone, one_mul]
      exact enorm_integral_le_lintegral_enorm _
    have hswapAE : AEMeasurable (fun p : ℂ × ℝ => ‖V (p.1 + p.2 • e) - V p.1‖ₑ)
        (volume.prod (volume.restrict (Set.uIoc 0 t))) :=
      ((hprodAE t V hV.aemeasurable).sub (hfstAE t V hV.aemeasurable)).enorm
    have hinner : ∀ s ∈ Set.uIoc (0 : ℝ) t,
        (∫⁻ z, ‖V (z + s • e) - V z‖ₑ) ≤ ENNReal.ofReal η := by
      intro s hs
      have hsε : |s| ≤ ε := le_trans (huIoc t s hs) htε
      have hint : Integrable (fun z : ℂ => V (z + s • e) - V z) volume :=
        (hV.comp_add_right (s • e)).sub hV
      rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
      exact ENNReal.ofReal_le_ofReal (hεle s hsε)
    calc (∫⁻ z in K, ‖t⁻¹ • (u (z + t • e) - u z) - D z‖ₑ)
        ≤ ∫⁻ z in K, (ENNReal.ofReal |t|⁻¹
            * ∫⁻ s in Set.uIoc 0 t, ‖V (z + s • e) - V z‖ₑ) := lintegral_mono_ae hptw
      _ = ENNReal.ofReal |t|⁻¹
            * ∫⁻ z in K, ∫⁻ s in Set.uIoc 0 t, ‖V (z + s • e) - V z‖ₑ :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ ENNReal.ofReal |t|⁻¹
            * ∫⁻ z, ∫⁻ s in Set.uIoc 0 t, ‖V (z + s • e) - V z‖ₑ :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal |t|⁻¹
            * ∫⁻ s in Set.uIoc 0 t, ∫⁻ z, ‖V (z + s • e) - V z‖ₑ := by
          rw [lintegral_lintegral_swap hswapAE]
      _ ≤ ENNReal.ofReal |t|⁻¹ * ∫⁻ _s in Set.uIoc 0 t, ENNReal.ofReal η :=
          mul_le_mul' le_rfl (lintegral_mono_ae
            ((ae_restrict_iff' measurableSet_uIoc).mpr
              (Filter.Eventually.of_forall hinner)))
      _ = ENNReal.ofReal |t|⁻¹ * (ENNReal.ofReal η * ENNReal.ofReal |t|) := by
          rw [setLIntegral_const, hvolI]
      _ = ENNReal.ofReal η := by
          rw [mul_comm (ENNReal.ofReal η) (ENNReal.ofReal |t|), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (abs_ne_zero.mpr ht0)]
          simp
  -- STEP 4: a strongly measurable surrogate for the difference quotients
  have hUint : Integrable (W.indicator u) volume :=
    memLp_one_iff_integrable.mp (hu W hδ₁Ω hWcomp)
  set τ : ℕ → ℝ := fun l => δ / ((l : ℝ) + 1) with hτdef
  have hτpos : ∀ l, 0 < τ l := fun l => div_pos hδpos (by positivity)
  have hτabs : ∀ l, |τ l| ≤ δ := by
    intro l
    rw [abs_of_pos (hτpos l), hτdef]
    exact div_le_self hδpos.le (by simp)
  have hτ0 : Filter.Tendsto τ Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul δ
    simpa [hτdef, div_eq_mul_inv] using h
  set Φ : ℕ → ℂ → ℂ :=
    fun l z => (τ l)⁻¹ • ((W.indicator u) (z + τ l • e) - (W.indicator u) z) with hΦdef
  have hΦint : ∀ l, Integrable (Φ l) volume := by
    intro l
    rw [hΦdef]
    have h1 : Integrable
        (fun z : ℂ => (W.indicator u) (z + τ l • e) - (W.indicator u) z) volume :=
      (hUint.comp_add_right (τ l • e)).sub hUint
    exact Integrable.smul (τ l)⁻¹ h1
  -- on `K` the surrogate agrees with the honest difference quotient
  have hΦeq : ∀ (l : ℕ), ∀ z ∈ K,
      Φ l z - V z = (τ l)⁻¹ • (u (z + τ l • e) - u z) - D z := by
    intro l z hzK
    simp only [hΦdef, hVdef]
    rw [Set.indicator_of_mem (hseg z hzK (τ l) (hτabs l)), Set.indicator_of_mem (hKW hzK),
      Set.indicator_of_mem (hKW hzK)]
  -- the surrogate converges to `V` in `L¹(K)`
  have hLp : Filter.Tendsto
      (fun l => eLpNorm (Φ l - V) 1 (volume.restrict K)) Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ζ hζ
    obtain ⟨η, hη, hηζ⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ζ := by
      rcases eq_or_ne ζ ⊤ with rfl | hζtop
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨ζ.toReal, ENNReal.toReal_pos hζ.ne' hζtop,
          le_of_eq (ENNReal.ofReal_toReal hζtop)⟩
    obtain ⟨δ', hδ'pos, _, hbd⟩ := hstep3 η hη
    have habs : Filter.Tendsto (fun l => |τ l|) Filter.atTop (nhds 0) := by
      simpa using hτ0.abs
    filter_upwards [habs.eventually (gt_mem_nhds hδ'pos)] with l hl
    have hlle : |τ l| ≤ δ' := hl.le
    have hcongr : ∀ᵐ z ∂(volume.restrict K),
        ‖(Φ l - V) z‖ₑ = ‖(τ l)⁻¹ • (u (z + τ l • e) - u z) - D z‖ₑ := by
      rw [ae_restrict_iff' hK.measurableSet]
      filter_upwards with z hzK
      rw [Pi.sub_apply, hΦeq l z hzK]
    calc eLpNorm (Φ l - V) 1 (volume.restrict K)
        = ∫⁻ z in K, ‖(Φ l - V) z‖ₑ := eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ z in K, ‖(τ l)⁻¹ • (u (z + τ l • e) - u z) - D z‖ₑ := lintegral_congr_ae hcongr
      _ ≤ ENNReal.ofReal η := hbd (τ l) (hτpos l).ne' hlle
      _ ≤ ζ := hηζ
  -- convergence in measure, then Riesz's a.e.-convergent subsequence
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (μ := volume.restrict K) one_ne_zero
      (fun l => (hΦint l).aestronglyMeasurable.restrict)
      hV.aestronglyMeasurable.restrict hLp).exists_seq_tendsto_ae
  refine ⟨fun i => τ (ns i), fun i => (hτpos (ns i)).ne',
    hτ0.comp hns.tendsto_atTop, ?_⟩
  rw [ae_restrict_iff' hK.measurableSet] at hae
  filter_upwards [hae] with z hz hzK
  have hlim := hz hzK
  have hVz : V z = D z := by rw [hVdef, Set.indicator_of_mem (hKW hzK)]
  have hfun : ∀ i, Φ (ns i) z - V z
      = (τ (ns i))⁻¹ • (u (z + τ (ns i) • e) - u z) - D z :=
    fun i => hΦeq (ns i) z hzK
  have hshift : Filter.Tendsto (fun i => Φ (ns i) z - V z) Filter.atTop (nhds 0) := by
    simpa using hlim.sub_const (V z)
  have : Filter.Tendsto
      (fun i => (τ (ns i))⁻¹ • (u (z + τ (ns i) • e) - u z) - D z)
      Filter.atTop (nhds 0) := by
    simpa [hfun] using hshift
  simpa using this.add_const (D z)
