import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.WirtingerPolarForm
import IwaniecManfredi.WeakPartialEqFDerivAE

/-- Equation (28) of the paper: writing (18) in polar coordinates, conjugating
it and eliminating `conj(H_r)` gives
`2 r H_r = -i p H_θ + (p-2) i e^{-2inθ} conj(H_θ)`, with
`e^{-2inθ} = (ξ̄/ξ)^n`.  Both sides are read through the Fréchet derivative of
`H`, so the hypothesis on `H` is exactly that it is differentiable almost
everywhere on `Ω`, which is what item (C2) of the paper's note gives for the
inverse of a quasiconformal homeomorphism; the conclusion, like (18) itself, is
an almost-everywhere identity. -/
theorem PolarEq28 (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (H : ℂ → ℂ) (hH : ∀ᵐ ξ : ℂ, ξ ∈ Ω → DifferentiableAt ℝ H ξ)
    (h18 : SolvesEq18 n p Ω H) :
    ∀ᵐ ξ, ξ ∈ Ω → ξ ≠ 0 →
      2 * ((‖ξ‖ : ℝ) : ℂ) * HRad H ξ
        = -Complex.I * (p : ℂ) * HAng H ξ
          + ((p : ℂ) - 2) * Complex.I * ((starRingEnd ℂ ξ / ξ) ^ n)
              * starRingEnd ℂ (HAng H ξ) := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  -- unpack the weak Wirtinger data of (18)
  obtain ⟨a, b, hww, h18ae⟩ := h18
  obtain ⟨Hx, Hy, hHL1, hHxL1, hHyL1, hwx, hwy, haf, hbf⟩ := hww
  -- the weak partials of `H` are its classical ones almost everywhere
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
  filter_upwards [hH, h18ae, key] with ξ hdξ h18ξ hkeyξ
  intro hΩξ hξ0
  have hd : DifferentiableAt ℝ H ξ := hdξ hΩξ
  obtain ⟨hbar, hz, -⟩ := WirtingerPolarForm H ξ hξ0 hd
  obtain ⟨hak, hbk⟩ := hkeyξ hΩξ
  have heq : DZbar H ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
      ((ξ / starRingEnd ℂ ξ) * DZ H ξ
        + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ (DZ H ξ)) := by
    rw [← hak, ← hbk]; exact h18ξ hΩξ hξ0
  have hr : (0:ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ0
  have hrc : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_ne_zero] using ne_of_gt hr
  have hcξ : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ0
  have hVne : ξ ^ n ≠ 0 := pow_ne_zero n hξ0
  have hWne : (starRingEnd ℂ ξ) ^ n ≠ 0 := pow_ne_zero n hcξ
  set r : ℂ := ((‖ξ‖ : ℝ) : ℂ) with hrdef
  set A := HRad H ξ with hAdef
  set B := HAng H ξ with hBdef
  set c : ℂ := ((1 / 2 - 1 / p : ℝ) : ℂ) with hcdef
  have hrconj : starRingEnd ℂ r = r := by rw [hrdef]; exact Complex.conj_ofReal _
  have hcconj : starRingEnd ℂ c = c := by rw [hcdef]; exact Complex.conj_ofReal _
  have hc : c * (2 * (p : ℂ)) = (p : ℂ) - 2 := by
    rw [hcdef]; push_cast; field_simp
  -- division-free polar forms
  have hbar2 : 2 * r ^ 2 * DZbar H ξ = (r * A + Complex.I * B) * ξ := by
    rw [hbar]; field_simp
  have hz2 : 2 * r ^ 2 * DZ H ξ = (r * A - Complex.I * B) * starRingEnd ℂ ξ := by
    rw [hz]; field_simp
  have hcz2 : 2 * r ^ 2 * starRingEnd ℂ (DZ H ξ)
      = (r * starRingEnd ℂ A + Complex.I * starRingEnd ℂ B) * ξ := by
    have h := congrArg (starRingEnd ℂ) hz2
    simp only [map_mul, map_sub, map_ofNat, map_pow, Complex.conj_I,
      Complex.conj_conj, hrdef, Complex.conj_ofReal] at h
    rw [h]; ring
  -- solve each derivative explicitly, so (18) can be cleared of denominators
  have hDZbar : DZbar H ξ = (r * A + Complex.I * B) * ξ / (2 * r ^ 2) := by
    rw [eq_div_iff (by simpa using hrc), mul_comm]; exact hbar2
  have hDZ : DZ H ξ = (r * A - Complex.I * B) * starRingEnd ℂ ξ / (2 * r ^ 2) := by
    rw [eq_div_iff (by simpa using hrc), mul_comm]; exact hz2
  have hcDZ : starRingEnd ℂ (DZ H ξ)
      = (r * starRingEnd ℂ A + Complex.I * starRingEnd ℂ B) * ξ / (2 * r ^ 2) := by
    rw [eq_div_iff (by simpa using hrc), mul_comm]; exact hcz2
  rw [hDZbar, hcDZ, hDZ] at heq
  -- E1, division-free
  have hE1 : ξ ^ n * (r * A + Complex.I * B)
      = c * (ξ ^ n * (r * A - Complex.I * B)
        + (starRingEnd ℂ ξ) ^ n * (r * starRingEnd ℂ A + Complex.I * starRingEnd ℂ B)) := by
    field_simp at heq
    linear_combination heq
  -- E2 is the conjugate of E1
  have hE2 : (starRingEnd ℂ ξ) ^ n * (r * starRingEnd ℂ A - Complex.I * starRingEnd ℂ B)
      = c * ((starRingEnd ℂ ξ) ^ n * (r * starRingEnd ℂ A + Complex.I * starRingEnd ℂ B)
        + ξ ^ n * (r * A - Complex.I * B)) := by
    have h := congrArg (starRingEnd ℂ) hE1
    simp only [map_mul, map_add, map_sub, map_pow, Complex.conj_I, Complex.conj_conj,
      hrconj, hcconj] at h
    linear_combination h
  -- the two right-hand sides coincide, which is the eliminated relation
  have hstar : ξ ^ n * (r * A + Complex.I * B)
      = (starRingEnd ℂ ξ) ^ n * (r * starRingEnd ℂ A - Complex.I * starRingEnd ℂ B) := by
    rw [hE1, hE2]; ring
  -- the paper's (28), still division-free
  have hident : ξ ^ n * ((1 - 2 * c) * (r * A) + Complex.I * B)
      = 2 * c * Complex.I * (starRingEnd ℂ ξ) ^ n * starRingEnd ℂ B := by
    linear_combination hE1 - c * hstar
  rw [div_pow]
  field_simp
  linear_combination (p : ℂ) * hident
    + (r * A * ξ ^ n + Complex.I * (starRingEnd ℂ ξ) ^ n * starRingEnd ℂ B) * hc
