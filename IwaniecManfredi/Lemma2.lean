import IwaniecManfredi.Preamble
import Mathlib.Analysis.MeanInequalitiesPow

/-- Lemma 2 of the paper (estimate (53)).  `F` is complex-valued, as the
Hölder spaces of Section 1 are spaces of complex-valued functions and Lemma 2
is applied in Section 6 to supply their Hölder condition.  The modulus
`|∇F(x)|` of hypothesis (ii) is rendered as the operator norm of the real
Fréchet derivative, which for real-valued `F` is exactly `|∇F(x)|`. -/
theorem Lemma2 {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : Convex ℝ U)
    (hUo : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α) (hα1 : α ≤ 1)
    (hFc : ContinuousOn F U) (hFd : ContDiffOn ℝ 1 F (U \ {0}))
    (hi : ∀ x ∈ U, ‖F x‖ ≤ M * ‖x‖ ^ α)
    (hii : ∀ x ∈ U \ {0}, ‖fderiv ℝ F x‖ ≤ M * ‖x‖ ^ (α - 1)) :
    ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ 5 * M * ‖x - y‖ ^ α := by
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simp [Real.zero_rpow (ne_of_gt hα)]
  have hd0 : 0 < ‖x - y‖ := by
    rw [norm_sub_pos_iff]
    exact hxy
  have hpα : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hcase : ‖y‖ ≤ 2 * ‖x - y‖
  · -- ## Case 1: `‖y‖ ≤ 2‖x-y‖`, where the two values of `F` are estimated separately
    -- and recombined by the power mean inequality.
    have hinv : ∀ t : ℝ, 0 ≤ t → (M * t ^ α) ^ (1 / α) = M ^ (1 / α) * t := by
      intro t ht
      rw [Real.mul_rpow hM (Real.rpow_nonneg ht α), ← Real.rpow_mul ht,
        mul_one_div_cancel (ne_of_gt hα), Real.rpow_one]
    have h1 : ‖F x‖ ^ (1 / α) ≤ M ^ (1 / α) * ‖x‖ := by
      rw [← hinv ‖x‖ (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hi x hx) (by positivity)
    have h2 : ‖F y‖ ^ (1 / α) ≤ M ^ (1 / α) * ‖y‖ := by
      rw [← hinv ‖y‖ (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hi y hy) (by positivity)
    have htri : ‖x‖ + ‖y‖ ≤ 5 * ‖x - y‖ := by
      have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        have h4 := norm_add_le (x - y) y
        simpa using h4
      linarith
    have hstep : (‖F x‖ ^ (1 / α) + ‖F y‖ ^ (1 / α)) ^ α
        ≤ (M ^ (1 / α) * (5 * ‖x - y‖)) ^ α := by
      refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hα)
      calc ‖F x‖ ^ (1 / α) + ‖F y‖ ^ (1 / α)
          ≤ M ^ (1 / α) * ‖x‖ + M ^ (1 / α) * ‖y‖ := by linarith
        _ = M ^ (1 / α) * (‖x‖ + ‖y‖) := by ring
        _ ≤ M ^ (1 / α) * (5 * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
    have hfinal : (M ^ (1 / α) * (5 * ‖x - y‖)) ^ α = M * 5 ^ α * ‖x - y‖ ^ α := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hM,
        one_div_mul_cancel (ne_of_gt hα), Real.rpow_one,
        Real.mul_rpow (by norm_num) (norm_nonneg _)]
      ring
    have hconst : (2 : ℝ) ^ (1 - α) * 5 ^ α ≤ 5 := by
      have he : (2 : ℝ) ^ (1 - α) * 5 ^ α = 2 * ((5 : ℝ) / 2) ^ α := by
        rw [Real.div_rpow (by norm_num) (by norm_num), Real.rpow_sub (by norm_num),
          Real.rpow_one]
        field_simp
      rw [he]
      have hle : ((5 : ℝ) / 2) ^ α ≤ ((5 : ℝ) / 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      rw [Real.rpow_one] at hle
      linarith
    -- the unweighted two-term power-mean inequality, specialised from mathlib's
    -- `NNReal.rpow_add_le_mul_rpow_add_rpow` at exponent `1/α` and then raised
    -- to the power `α`
    have hpm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        a + b ≤ (2 : ℝ) ^ (1 - α) * (a ^ (1 / α) + b ^ (1 / α)) ^ α := by
      intro a b ha hb
      have hα0 : α ≠ 0 := ne_of_gt hα
      have hab : (0 : ℝ) ≤ a + b := by linarith
      have hs1 : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
      have key := NNReal.rpow_add_le_mul_rpow_add_rpow a.toNNReal b.toNNReal hs1
      have hcoe := (NNReal.coe_le_coe (r₁ := (a.toNNReal + b.toNNReal) ^ (1 / α))
        (r₂ := (2 : NNReal) ^ (1 / α - 1)
          * (a.toNNReal ^ (1 / α) + b.toNNReal ^ (1 / α)))).mpr key
      push_cast [NNReal.coe_rpow, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] at hcoe
      have hmono := Real.rpow_le_rpow (by positivity) hcoe hα.le
      have hL : ((a + b) ^ (1 / α)) ^ α = a + b := by
        rw [← Real.rpow_mul hab, one_div_mul_cancel hα0, Real.rpow_one]
      have hR : ((2 : ℝ) ^ (1 / α - 1) * (a ^ (1 / α) + b ^ (1 / α))) ^ α
          = (2 : ℝ) ^ (1 - α) * (a ^ (1 / α) + b ^ (1 / α)) ^ α := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
        congr 2
        field_simp
      rwa [hL, hR] at hmono
    calc ‖F x - F y‖ ≤ ‖F x‖ + ‖F y‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ (1 - α) * (‖F x‖ ^ (1 / α) + ‖F y‖ ^ (1 / α)) ^ α :=
          hpm ‖F x‖ ‖F y‖ (norm_nonneg _) (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ (1 - α) * (M ^ (1 / α) * (5 * ‖x - y‖)) ^ α :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = ((2 : ℝ) ^ (1 - α) * 5 ^ α) * (M * ‖x - y‖ ^ α) := by
          rw [hfinal]
          ring
      _ ≤ 5 * (M * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = 5 * M * ‖x - y‖ ^ α := by ring
  · -- ## Case 2: `‖y‖ > 2‖x-y‖`, where the whole segment stays off the origin and the
    -- mean value inequality applies with the constant `M ‖x-y‖^{α-1}`.
    rw [not_le] at hcase
    have hUmin : IsOpen (U \ {(0 : EuclideanSpace ℝ (Fin n))}) :=
      hUo.sdiff isClosed_singleton
    have hseg : ∀ z ∈ segment ℝ y x,
        z ∈ U \ {(0 : EuclideanSpace ℝ (Fin n))} ∧ ‖x - y‖ ≤ ‖z‖ := by
      intro z hz
      obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
      have hzU : z ∈ U := hU.segment_subset hy hx ⟨a, b, ha, hb, hab, hzeq⟩
      have hzy : z - y = b • (x - y) := by
        rw [← hzeq, show a = 1 - b from by linarith]
        module
      have hnzy : ‖z - y‖ ≤ ‖x - y‖ := by
        rw [hzy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
        calc b * ‖x - y‖ ≤ 1 * ‖x - y‖ :=
              mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
          _ = ‖x - y‖ := one_mul _
      have hylow : ‖y‖ ≤ ‖z‖ + ‖z - y‖ := by
        calc ‖y‖ = ‖z - (z - y)‖ := by
              congr 1
              abel
          _ ≤ ‖z‖ + ‖z - y‖ := norm_sub_le _ _
      have hzlow : ‖x - y‖ < ‖z‖ := by linarith
      refine ⟨⟨hzU, ?_⟩, le_of_lt hzlow⟩
      simp only [Set.mem_singleton_iff]
      intro hcon
      rw [hcon, norm_zero] at hzlow
      linarith
    have hder : ∀ z ∈ segment ℝ y x,
        HasFDerivWithinAt F (fderiv ℝ F z) (segment ℝ y x) z := by
      intro z hz
      have hzU := (hseg z hz).1
      have hdiff : DifferentiableAt ℝ F z :=
        ((hFd.differentiableOn (by norm_num)) z hzU).differentiableAt (hUmin.mem_nhds hzU)
      exact hdiff.hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ z ∈ segment ℝ y x,
        ‖fderiv ℝ F z‖ ≤ M * ‖x - y‖ ^ (α - 1) := by
      intro z hz
      refine le_trans (hii z (hseg z hz).1) (mul_le_mul_of_nonneg_left ?_ hM)
      exact Real.rpow_le_rpow_of_nonpos hd0 (hseg z hz).2 (by linarith)
    have hmv := (convex_segment y x).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hder hbound (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)
    have hpow : ‖x - y‖ ^ (α - 1) * ‖x - y‖ = ‖x - y‖ ^ α := by
      have h := Real.rpow_add hd0 (α - 1) 1
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    calc ‖F x - F y‖ ≤ M * ‖x - y‖ ^ (α - 1) * ‖x - y‖ := hmv
      _ = M * ‖x - y‖ ^ α := by rw [mul_assoc, hpow]
      _ = 1 * (M * ‖x - y‖ ^ α) := by ring
      _ ≤ 5 * (M * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 5 * M * ‖x - y‖ ^ α := by ring
