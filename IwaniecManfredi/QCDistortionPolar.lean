import IwaniecManfredi.QuasiregularOn
import IwaniecManfredi.Jac
import IwaniecManfredi.WirtingerPolarForm
import IwaniecManfredi.WeakPartialEqFDerivAE

/-- The quasiregularity estimates (26) and (27) of Section 4 of the paper, in
polar form: `K⁻¹|H_r|² ≤ J ≤ K|H_r|²` and
`(1+K⁻²)|H_r|² ≤ 2|H_ξ|² + 2|H_ξ̄|² ≤ (1+K²)|H_r|²`.  Both are two faces of
the single inequality `|H_ξ| + |H_ξ̄| ≤ K(|H_ξ| - |H_ξ̄|)`, which is the
distortion inequality (11) rearranged, so they belong in one node.  Every
quantity in them is read through the Fréchet derivative of `H`, so the
hypothesis on `H` is that it is differentiable almost everywhere on `Ω`, which
is what item (C2) of the paper's note gives for the inverse of a quasiconformal
homeomorphism; the conclusion, like the distortion inequality it rearranges, is
an almost-everywhere statement. -/
theorem QCDistortionPolar (K : ℝ) (Ω : Set ℂ) (H : ℂ → ℂ) (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hH : ∀ᵐ ξ : ℂ, ξ ∈ Ω → DifferentiableAt ℝ H ξ)
    (hqr : QuasiregularOn K Ω H) :
    ∀ᵐ ξ, ξ ∈ Ω → ξ ≠ 0 →
      (K⁻¹ * ‖HRad H ξ‖ ^ 2 ≤ Jac H ξ ∧ Jac H ξ ≤ K * ‖HRad H ξ‖ ^ 2) ∧
      ((1 + (K ^ 2)⁻¹) * ‖HRad H ξ‖ ^ 2 ≤ 2 * ‖DZ H ξ‖ ^ 2 + 2 * ‖DZbar H ξ‖ ^ 2 ∧
        2 * ‖DZ H ξ‖ ^ 2 + 2 * ‖DZbar H ξ‖ ^ 2 ≤ (1 + K ^ 2) * ‖HRad H ξ‖ ^ 2) := by
  obtain ⟨-, -, a, b, hww, hdist⟩ := hqr
  obtain ⟨Hx, Hy, hHL1, hHxL1, hHyL1, hwx, hwy, haf, hbf⟩ := hww
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  -- the weak Wirtinger derivatives of `H` are its classical ones almost everywhere
  have hD : ∀ j : Fin 2,
      MemLpLocOn 1 Ω ((fun j : Fin 2 => if j = 0 then Hx else Hy) j) := by
    intro j; fin_cases j
    · simpa using hHxL1
    · simpa using hHyL1
  have hweak : ∀ j : Fin 2,
      IsWeakPartialOn Ω j H ((fun j : Fin 2 => if j = 0 then Hx else Hy) j) := by
    intro j; fin_cases j
    · simpa using hwx
    · simpa using hwy
  have hbr := WeakPartialEqFDerivAE Ω hΩ H (fun j : Fin 2 => if j = 0 then Hx else Hy)
    hHL1 hD hweak hH
  have key : ∀ᵐ ξ : ℂ, ξ ∈ Ω → a ξ = DZ H ξ ∧ b ξ = DZbar H ξ := by
    filter_upwards [hbr 0, hbr 1] with ξ h0 h1
    intro hξ
    have e0 : Hx ξ = fderiv ℝ H ξ 1 := by simpa [PartialWord] using h0 hξ
    have e1 : Hy ξ = fderiv ℝ H ξ Complex.I := by simpa [PartialWord] using h1 hξ
    exact ⟨by simp only [haf ξ, e0, e1, DZ], by simp only [hbf ξ, e0, e1, DZbar]⟩
  filter_upwards [hH, hdist, key] with ξ hdξ hdistξ hkeyξ
  intro hΩξ hξ0
  have hd : DifferentiableAt ℝ H ξ := hdξ hΩξ
  obtain ⟨hak, hbk⟩ := hkeyξ hΩξ
  have hb : ‖DZbar H ξ‖ ≤ ((K - 1) / (K + 1)) * ‖DZ H ξ‖ := by
    rw [← hak, ← hbk]; exact hdistξ hΩξ
  set a := ‖DZ H ξ‖ with ha
  set b := ‖DZbar H ξ‖ with hbb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  -- the rearranged distortion inequality  a + b ≤ K (a - b)
  have hKey : a + b ≤ K * (a - b) := by
    have hKp : (0:ℝ) < K + 1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hKp] at hb
    nlinarith [hb]
  have hab : b ≤ a := by nlinarith [hKey]
  -- the polar identity and the two triangle bounds on ‖H_r‖
  obtain ⟨-, -, hpolar⟩ := WirtingerPolarForm H ξ hξ0 hd
  have hn0 : (0:ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ0
  have hu1 : ‖ξ / ((‖ξ‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0,
      div_self (ne_of_gt hn0)]
  have hu2 : ‖starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0,
      RCLike.norm_conj, div_self (ne_of_gt hn0)]
  have hupper : ‖HRad H ξ‖ ≤ a + b := by
    rw [hpolar]
    calc ‖DZ H ξ * (ξ / ((‖ξ‖ : ℝ) : ℂ)) + DZbar H ξ * (starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ))‖
        ≤ ‖DZ H ξ * (ξ / ((‖ξ‖ : ℝ) : ℂ))‖
            + ‖DZbar H ξ * (starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ))‖ := norm_add_le _ _
      _ = a + b := by rw [norm_mul, norm_mul, hu1, hu2]; ring
  have hlower : a - b ≤ ‖HRad H ξ‖ := by
    rw [hpolar]
    have h := norm_sub_norm_le (DZ H ξ * (ξ / ((‖ξ‖ : ℝ) : ℂ)))
      (- (DZbar H ξ * (starRingEnd ℂ ξ / ((‖ξ‖ : ℝ) : ℂ))))
    rw [norm_neg, norm_mul, norm_mul, hu1, hu2, sub_neg_eq_add] at h
    simpa using h
  have hr0 : 0 ≤ ‖HRad H ξ‖ := norm_nonneg _
  have hJ : Jac H ξ = a ^ 2 - b ^ 2 := rfl
  have hK2 : (0:ℝ) < K ^ 2 := by positivity
  -- the single inequality, squared:  (a+b)^2 ≤ K^2 (a-b)^2
  have hsq : (a + b) ^ 2 ≤ K ^ 2 * (a - b) ^ 2 := by
    have h := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ a + b) hKey
    nlinarith [h]
  have hRup : ‖HRad H ξ‖ ^ 2 ≤ (a + b) ^ 2 := by nlinarith [hupper, hr0]
  have hRlo : (a - b) ^ 2 ≤ ‖HRad H ξ‖ ^ 2 := by nlinarith [hlower, hab, hr0]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hJ, inv_mul_le_iff₀ hK0]
    nlinarith [hupper, hr0, hKey, ha0, hb0, hab]
  · rw [hJ]
    have h1 : (a + b) * (a - b) ≤ K * (a - b) * (a - b) :=
      mul_le_mul_of_nonneg_right hKey (by linarith)
    have h2 : K * (a - b) ^ 2 ≤ K * ‖HRad H ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hRlo (le_of_lt hK0)
    nlinarith [h1, h2]
  · have hinv : (K ^ 2)⁻¹ * ‖HRad H ξ‖ ^ 2 ≤ (a - b) ^ 2 := by
      rw [inv_mul_le_iff₀ hK2]
      nlinarith [hRup, hsq]
    nlinarith [hRup, hinv]
  · have h2 : K ^ 2 * (a - b) ^ 2 ≤ K ^ 2 * ‖HRad H ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hRlo (le_of_lt hK2)
    nlinarith [hRlo, hsq, h2]
