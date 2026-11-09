import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-- The Wirtinger derivatives of a real power of the modulus:
`∂(|ξ|^μ)/∂ξ = (μ/2)|ξ|^μ/ξ` and `∂(|ξ|^μ)/∂ξ̄ = (μ/2)|ξ|^μ/ξ̄`, together with
smoothness off the origin.  The factor `|ξ|^{λ_k+n-k}` of the series (19) is of
this form, so the rule is what differentiates each summand; the integer power
rules do not cover it, because the exponent is a real number. -/
theorem WirtingerModulusPowerRule (μ : ℝ) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ)) ξ ∧
    DZ (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ)) ξ
        = ((μ / 2 : ℝ) : ℂ) * ((‖ξ‖ ^ μ : ℝ) : ℂ) / ξ ∧
    DZbar (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ)) ξ
        = ((μ / 2 : ℝ) : ℂ) * ((‖ξ‖ ^ μ : ℝ) : ℂ) / starRingEnd ℂ ξ := by
  have hn0 : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hnpos : (0:ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hsq0 : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  have hns : (‖ξ‖ : ℝ) ^ 2 = ξ.re ^ 2 + ξ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  -- `‖z‖ ^ μ` rewritten as an rpow of the square: Mathlib has `contDiffAt_norm`
  -- but no `hasFDerivAt_norm`, so we differentiate `‖z‖^2`, which is smooth.
  have hrw : (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ))
      = (fun z : ℂ => (((‖z‖ ^ 2 : ℝ) ^ (μ / 2) : ℝ) : ℂ)) := by
    funext z
    rcases eq_or_ne z 0 with rfl | hz
    · by_cases hμ : μ = 0
      · simp [hμ]
      · simp [Real.zero_rpow hμ, Real.zero_rpow (by simpa using hμ : μ / 2 ≠ 0)]
    · have h : ((‖z‖ ^ 2 : ℝ) ^ (μ / 2) : ℝ) = ‖z‖ ^ μ := by
        rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        push_cast
        ring
      rw [h]
  have hsqcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖ ^ 2) ξ :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hsqfd : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2) (2 • innerSL ℝ ξ) ξ := by
    -- `ContDiff.differentiable` wants `n ≠ 0`, so pin `n = 1` explicitly.
    have hcd : ContDiff ℝ 1 (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
    have hdiff := hcd.differentiable (by norm_num) ξ
    rw [← fderiv_norm_sq_apply (F := ℂ) ξ]
    exact hdiff.hasFDerivAt
  have hpart1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ)) ξ := by
    rw [hrw]
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp ξ
      (hsqcd.rpow_const_of_ne (by simpa using hsq0))
  have hfd : HasFDerivAt (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) ^ (μ / 2) : ℝ))
      (((μ / 2) * (‖ξ‖ ^ 2) ^ (μ / 2 - 1)) • (2 • innerSL ℝ ξ)) ξ :=
    hsqfd.rpow_const (Or.inl (by simpa using hsq0))
  have hfdC : HasFDerivAt (fun z : ℂ => (((‖z‖ ^ 2 : ℝ) ^ (μ / 2) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp
        (((μ / 2) * (‖ξ‖ ^ 2) ^ (μ / 2 - 1)) • (2 • innerSL ℝ ξ))) ξ :=
    Complex.ofRealCLM.hasFDerivAt.comp ξ hfd
  have hd : ∀ v : ℂ, fderiv ℝ (fun z : ℂ => ((‖z‖ ^ μ : ℝ) : ℂ)) ξ v
      = ((μ / 2 * (‖ξ‖ ^ 2) ^ (μ / 2 - 1) * (2 * (v.re * ξ.re + v.im * ξ.im)) : ℝ) : ℂ) := by
    intro v
    rw [hrw, hfdC.fderiv]
    simp
    all_goals ring
  -- rpow bookkeeping, in PRODUCT form so no division enters the final ring goal
  -- (`ring` cannot cancel `x^2 * (x⁻¹)^2` without knowing `x ≠ 0`).
  have hpowR : ((‖ξ‖ ^ 2 : ℝ) ^ (μ / 2 - 1)) * ‖ξ‖ ^ 2 = ‖ξ‖ ^ μ := by
    rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ),
      ← Real.rpow_add hnpos]
    congr 1
    push_cast
    ring
  have hpow2 : (((‖ξ‖ ^ 2 : ℝ) ^ (μ / 2 - 1) : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2
      = ((‖ξ‖ ^ μ : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hpowR
  have hcjeq : ((ξ.re : ℂ) - (ξ.im : ℂ) * Complex.I) = starRingEnd ℂ ξ := by
    apply Complex.ext <;> simp
  have hcj : ((ξ.re : ℂ) - (ξ.im : ℂ) * Complex.I) * ξ = (‖ξ‖ : ℂ) ^ 2 := by
    rw [hcjeq, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hcj' : ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I) * starRingEnd ℂ ξ
      = (‖ξ‖ : ℂ) ^ 2 := by
    have h : ((ξ.re : ℂ) + (ξ.im : ℂ) * Complex.I) = ξ := (Complex.re_add_im ξ)
    rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  refine ⟨hpart1, ?_, ?_⟩
  · rw [DZ, hd 1, hd Complex.I, eq_div_iff hξ]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    linear_combination
      ((μ : ℂ) / 2 * (((‖ξ‖ ^ 2 : ℝ) ^ (μ / 2 - 1) : ℝ) : ℂ)) * hcj
        + ((μ : ℂ) / 2) * hpow2
  · have hcne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
    rw [DZbar, hd 1, hd Complex.I, eq_div_iff hcne]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    linear_combination
      ((μ : ℂ) / 2 * (((‖ξ‖ ^ 2 : ℝ) ^ (μ / 2 - 1) : ℝ) : ℂ)) * hcj'
        + ((μ : ℂ) / 2) * hpow2
