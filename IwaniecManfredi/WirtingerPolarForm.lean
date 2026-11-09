import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar
import IwaniecManfredi.HRad
import IwaniecManfredi.HAng

/-- The polar transformation formulas opening Section 4 of the paper:
`H_ξ̄ = (1/2)(H_r + (i/r) H_θ) e^{iθ}` and
`H_ξ = (1/2)(H_r - (i/r) H_θ) e^{-iθ}`, together with the equivalent inverse
relation `H_r = H_ξ e^{iθ} + H_ξ̄ e^{-iθ}` that the distortion estimates (26),
(27) and the Fourier computation of Section 4 use.  Here `e^{iθ} = ξ/|ξ|`. -/
theorem WirtingerPolarForm (H : ℂ → ℂ) (ξ : ℂ) (hξ : ξ ≠ 0)
    (hH : DifferentiableAt ℝ H ξ) :
    DZbar H ξ
        = (1 / 2 : ℂ) * (HRad H ξ + (Complex.I / ((‖ξ‖ : ℝ) : ℂ)) * HAng H ξ)
            * (ξ / ((‖ξ‖ : ℝ) : ℂ)) ∧
      DZ H ξ
        = (1 / 2 : ℂ) * (HRad H ξ - (Complex.I / ((‖ξ‖ : ℝ) : ℂ)) * HAng H ξ)
            * (starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ)) ∧
      HRad H ξ
        = DZ H ξ * (ξ / ((‖ξ‖ : ℝ) : ℂ))
            + DZbar H ξ * (starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ)) := by
  -- The Wirtinger decomposition of the real Fréchet differential.  Inlined here
  -- as a `have` rather than promoted to a helper node: FILESPEC:126-129 makes
  -- that promotion a proof-body edit, so it can be done later at no cost.
  have hdecomp : ∀ v : ℂ,
      fderiv ℝ H ξ v = DZ H ξ * v + DZbar H ξ * (starRingEnd ℂ v) := by
    intro v
    obtain ⟨x, y, hvv⟩ : ∃ x y : ℝ, v = (x : ℂ) + (y : ℂ) * Complex.I :=
      ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
    subst hvv
    have hsm : ((x : ℂ) + (y : ℂ) * Complex.I) = x • (1 : ℂ) + y • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
    have hlin : fderiv ℝ H ξ ((x : ℂ) + (y : ℂ) * Complex.I)
        = (x : ℂ) * fderiv ℝ H ξ 1 + (y : ℂ) * fderiv ℝ H ξ Complex.I := by
      rw [hsm, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hconj : (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)
        = (x : ℂ) - (y : ℂ) * Complex.I := by
      simp [sub_eq_add_neg]
    rw [hlin, hconj, DZ, DZbar]
    linear_combination ((y : ℂ) * fderiv ℝ H ξ Complex.I) * Complex.I_sq
  have hr0 : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_ne_zero, norm_ne_zero_iff] using hξ
  have hmul : ξ * (starRingEnd ℂ ξ) = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hcr : (starRingEnd ℂ) (ξ / ((‖ξ‖ : ℝ) : ℂ))
      = (starRingEnd ℂ ξ) / ((‖ξ‖ : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal]
  have hHRad : HRad H ξ
      = DZ H ξ * (ξ / ((‖ξ‖ : ℝ) : ℂ))
        + DZbar H ξ * ((starRingEnd ℂ ξ) / ((‖ξ‖ : ℝ) : ℂ)) := by
    rw [HRad, hdecomp, hcr]
  have hHAng : HAng H ξ
      = DZ H ξ * (Complex.I * ξ) - DZbar H ξ * (Complex.I * (starRingEnd ℂ ξ)) := by
    rw [HAng, hdecomp]
    have hc : (starRingEnd ℂ) (Complex.I * ξ) = -(Complex.I * (starRingEnd ℂ ξ)) := by simp
    rw [hc]; ring
  refine ⟨?_, ?_, hHRad⟩
  · rw [hHRad, hHAng]
    field_simp
    linear_combination (-2 * DZbar H ξ) * hmul
      - (DZ H ξ * ξ - DZbar H ξ * (starRingEnd ℂ ξ)) * ξ * Complex.I_sq
  · rw [hHRad, hHAng]
    field_simp
    linear_combination (-2 * DZ H ξ) * hmul
      + (DZ H ξ * ξ - DZbar H ξ * (starRingEnd ℂ ξ)) * (starRingEnd ℂ ξ) * Complex.I_sq
