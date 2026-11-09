import IwaniecManfredi.Preamble

/-- Differentiability across an isolated bad point: a function continuous on an
open set and differentiable off one point of it, whose derivative has a limit
`L` at that point, is differentiable there with derivative `L`, and its
derivative is continuous there.  This is the step Section 6 of the paper never
states -- it is what upgrades `C^1` to `C^k` across the singular point in (52),
where for `|ν| = m+1 ≤ k` the exponent `d - m = k-1+α-m ≥ α > 0` makes the
derivative tend to `0` -- and it is also the continuity at the singular point
that the hypothesis `F` continuous of the paper's Lemma 2 presumes. -/
theorem FDerivAcrossPoint (Ω : Set ℂ) (hΩ : IsOpen Ω) (z₀ : ℂ) (h0 : z₀ ∈ Ω)
    (g : ℂ → ℂ) (L : ℂ →L[ℝ] ℂ)
    (hcont : ContinuousOn g Ω)
    (hdiff : ∀ z ∈ Ω \ {z₀}, DifferentiableAt ℝ g z)
    (hlim : Filter.Tendsto (fun z => fderiv ℝ g z)
      (nhdsWithin z₀ (Ω \ {z₀})) (nhds L)) :
    HasFDerivAt g L z₀ ∧ ContinuousWithinAt (fun z => fderiv ℝ g z) Ω z₀ := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hΩ z₀ h0
  -- ## The `δ`-extraction from (H3)
  have hdelta : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      ∀ w : ℂ, 0 < ‖w - z₀‖ → ‖w - z₀‖ < δ → ‖fderiv ℝ g w - L‖ ≤ ε := by
    intro ε hε
    have hnhd : {M : ℂ →L[ℝ] ℂ | ‖M - L‖ ≤ ε} ∈ nhds L := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds L hε) ?_
      intro M hM
      simp only [Metric.mem_ball, dist_eq_norm] at hM
      exact le_of_lt hM
    have hmem := hlim.eventually hnhd
    rw [Filter.eventually_iff, mem_nhdsWithin] at hmem
    obtain ⟨U, hUopen, hz₀U, hUsub⟩ := hmem
    obtain ⟨rU, hrU, hrUsub⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀U
    refine ⟨min r rU, lt_min hr hrU, min_le_left _ _, ?_⟩
    intro w hw1 hw2
    have hwU : w ∈ U := by
      refine hrUsub ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hw2 (min_le_right _ _)
    have hwΩ : w ∈ Ω := by
      refine hrsub ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hw2 (min_le_left _ _)
    have hwne : w ≠ z₀ := by
      intro hc
      rw [hc] at hw1
      simp at hw1
    exact hUsub ⟨hwU, hwΩ, by simpa using hwne⟩
  -- ## Step 1: the radial mean value estimate
  have hstep1 : ∀ (ε δ : ℝ), 0 < ε → 0 < δ → δ ≤ r →
      (∀ w : ℂ, 0 < ‖w - z₀‖ → ‖w - z₀‖ < δ → ‖fderiv ℝ g w - L‖ ≤ ε) →
      ∀ z : ℂ, ‖z - z₀‖ < δ → ‖g z - g z₀ - L (z - z₀)‖ ≤ ε * ‖z - z₀‖ := by
    intro ε δ hε hδ hδr hbound z hz
    by_cases hzz : z = z₀
    · subst hzz
      simp
    have hznorm : (0 : ℝ) < ‖z - z₀‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hzz
    -- the point `z_t` and the segment estimate, for `0 < t ≤ 1`
    have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 →
        ‖g z - g (z₀ + (t : ℂ) * (z - z₀)) - L (z - (z₀ + (t : ℂ) * (z - z₀)))‖
          ≤ ε * ‖z - (z₀ + (t : ℂ) * (z - z₀))‖ := by
      intro t ht ht1
      -- every point of the segment is at distance in `[t‖z-z₀‖, ‖z-z₀‖]` from `z₀`
      have hsegpt : ∀ x ∈ segment ℝ (z₀ + (t : ℂ) * (z - z₀)) z,
          0 < ‖x - z₀‖ ∧ ‖x - z₀‖ < δ := by
        intro x hx
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
        have habc : (a : ℂ) + (b : ℂ) = 1 := by
          rw [← Complex.ofReal_add, hab]
          norm_num
        have hxz : a • (z₀ + (t : ℂ) * (z - z₀)) + b • z - z₀
            = ((a * t + b : ℝ) : ℂ) * (z - z₀) := by
          simp only [Complex.real_smul]
          push_cast
          linear_combination z₀ * habc
        have hcoef1 : t ≤ a * t + b := by nlinarith [ha, hb, ht1]
        have hcoef2 : a * t + b ≤ 1 := by nlinarith [ha, hb, ht1, ht]
        have hnx : ‖a • (z₀ + (t : ℂ) * (z - z₀)) + b • z - z₀‖
            = (a * t + b) * ‖z - z₀‖ := by
          rw [hxz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by nlinarith [ht] : (0 : ℝ) < a * t + b)]
        refine ⟨?_, ?_⟩
        · rw [hnx]
          have : (0 : ℝ) < a * t + b := by nlinarith [ht]
          positivity
        · rw [hnx]
          calc (a * t + b) * ‖z - z₀‖ ≤ 1 * ‖z - z₀‖ :=
                mul_le_mul_of_nonneg_right hcoef2 (norm_nonneg _)
            _ = ‖z - z₀‖ := one_mul _
            _ < δ := hz
      have hfd : ∀ x ∈ segment ℝ (z₀ + (t : ℂ) * (z - z₀)) z,
          HasFDerivWithinAt g (fderiv ℝ g x) (segment ℝ (z₀ + (t : ℂ) * (z - z₀)) z) x := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hsegpt x hx
        have hxΩ : x ∈ Ω := by
          refine hrsub ?_
          rw [Metric.mem_ball, dist_eq_norm]
          exact lt_of_lt_of_le hx2 hδr
        have hxne : x ≠ z₀ := by
          intro hc
          rw [hc] at hx1
          simp at hx1
        exact ((hdiff x ⟨hxΩ, by simpa using hxne⟩).hasFDerivAt).hasFDerivWithinAt
      have hbd : ∀ x ∈ segment ℝ (z₀ + (t : ℂ) * (z - z₀)) z, ‖fderiv ℝ g x - L‖ ≤ ε := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hsegpt x hx
        exact hbound x hx1 hx2
      exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hfd hbd
        (convex_segment (z₀ + (t : ℂ) * (z - z₀)) z) (left_mem_segment ℝ _ _)
        (right_mem_segment ℝ _ _)
    -- pass `t → 0` along `t_k = 1/(k+1)`
    obtain ⟨w, hwdef⟩ : ∃ q : ℕ → ℂ,
        q = fun k : ℕ => z₀ + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (z - z₀) := ⟨_, rfl⟩
    have htk : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hwtend : Filter.Tendsto w Filter.atTop (nhds z₀) := by
      rw [hwdef]
      have h1 : Filter.Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ))
          Filter.atTop (nhds 0) := by
        have hc := (Complex.continuous_ofReal.tendsto 0).comp htk
        rw [Complex.ofReal_zero] at hc
        exact hc
      have h2 := (h1.mul_const (z - z₀)).const_add z₀
      simpa using h2
    have hwpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := by
      intro k
      positivity
    have hwle : ∀ k : ℕ, (1 / ((k : ℝ) + 1) : ℝ) ≤ 1 := by
      intro k
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hwΩ : ∀ k : ℕ, w k ∈ Ω := by
      intro k
      refine hrsub ?_
      rw [Metric.mem_ball, dist_eq_norm, hwdef]
      have hn : ‖z₀ + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (z - z₀) - z₀‖
          = (1 / ((k : ℝ) + 1)) * ‖z - z₀‖ := by
        rw [show z₀ + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (z - z₀) - z₀
            = ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * (z - z₀) by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos k)]
      simp only [hn]
      calc (1 / ((k : ℝ) + 1)) * ‖z - z₀‖ ≤ 1 * ‖z - z₀‖ :=
            mul_le_mul_of_nonneg_right (hwle k) (norm_nonneg _)
        _ = ‖z - z₀‖ := one_mul _
        _ < δ := hz
        _ ≤ r := hδr
    have hgw : Filter.Tendsto (fun k => g (w k)) Filter.atTop (nhds (g z₀)) := by
      refine (hcont z₀ h0).tendsto.comp ?_
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hwtend
        (Filter.Eventually.of_forall hwΩ)
    -- the two sides converge
    have hA : Filter.Tendsto (fun k => ‖g z - g (w k) - L (z - w k)‖) Filter.atTop
        (nhds ‖g z - g z₀ - L (z - z₀)‖) := by
      refine Filter.Tendsto.norm ?_
      exact (tendsto_const_nhds.sub hgw).sub (L.continuous.tendsto _ |>.comp
        (tendsto_const_nhds.sub hwtend))
    have hB : Filter.Tendsto (fun k => ε * ‖z - w k‖) Filter.atTop (nhds (ε * ‖z - z₀‖)) :=
      (Filter.Tendsto.norm (tendsto_const_nhds.sub hwtend)).const_mul ε
    refine le_of_tendsto_of_tendsto' hA hB ?_
    intro k
    rw [hwdef]
    exact hseg (1 / ((k : ℝ) + 1)) (hwpos k) (hwle k)
  -- ## Step 2: `HasFDerivAt g L z₀`
  have hstep2 : HasFDerivAt g L z₀ := by
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨δ, hδ, hδr, hbound⟩ := hdelta c hc
    filter_upwards [Metric.ball_mem_nhds z₀ hδ] with x hx
    have hx' : ‖x - z₀‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx
    exact hstep1 c δ hc hδ hδr hbound x hx'
  refine ⟨hstep2, ?_⟩
  -- ## Step 3: continuity of the derivative at `z₀` within `Ω`
  have hfd0 : fderiv ℝ g z₀ = L := hstep2.fderiv
  rw [ContinuousWithinAt, hfd0]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδr, hbound⟩ := hdelta (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hxΩ hxd
  rw [dist_eq_norm] at hxd ⊢
  by_cases hxz : x = z₀
  · rw [hxz, hfd0]
    simpa using hε
  · have hx1 : (0 : ℝ) < ‖x - z₀‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hxz
    have := hbound x hx1 hxd
    calc ‖fderiv ℝ g x - L‖ ≤ ε / 2 := this
      _ < ε := by linarith
