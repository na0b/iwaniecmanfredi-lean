import IwaniecManfredi.ExtremalH

/-- The two identities Section 7 of the paper extracts from (54) before
anything else: the polar form `H(r e^{iθ}) = r^{1/d}(e^{iθ} + ε e^{-3iθ})`,
which is the form in which the injectivity of `H` is read off, and the scaling
identity `t H(ξ) = H(t^d ξ)`, which the paper uses to derive the homogeneity
(57) of the inverse `f = H⁻¹`. -/
theorem ExtremalPolarForm (p : ℝ) (hp : 1 < p) :
    (∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      ExtremalH p ((r : ℂ) * Complex.exp (θ * Complex.I))
        = ((r ^ (1 / DExp p) : ℝ) : ℂ) *
          (Complex.exp (θ * Complex.I)
            + ((EpsCoef 1 2 p : ℝ) : ℂ) * Complex.exp (-(3 * θ) * Complex.I))) ∧
    (∀ t : ℝ, 0 < t → ∀ ξ : ℂ,
      (t : ℂ) * ExtremalH p ξ = ExtremalH p (((t ^ DExp p : ℝ) : ℂ) * ξ)) := by
  have hdpos : 0 < DExp p := by
    unfold DExp
    have h1 : 0 < 1 / (p - 1) := by positivity
    have h2 : 0 ≤ Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2) := Real.sqrt_nonneg _
    linarith
  constructor
  · intro r hr θ
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    have hrne : (r : ℂ) ≠ 0 := by simpa using hr.ne'
    have hr3 : ((r : ℂ)) ^ 3 ≠ 0 := pow_ne_zero _ hrne
    have hexp3 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 3
        = Complex.exp ((3 * (θ : ℂ)) * Complex.I) := by
      rw [← Complex.exp_nat_mul]; ring_nf
    have q1 : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / (r : ℂ)
        = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [mul_comm, mul_div_assoc, div_self hrne, mul_one]
    have q2 : ((r : ℂ)) ^ 3 / (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3)
        = Complex.exp (-(3 * (θ : ℂ)) * Complex.I) := by
      rw [mul_pow, hexp3, div_mul_cancel_left₀ hr3, ← Complex.exp_neg]
      ring_nf
    unfold ExtremalH
    rw [hnorm, q1, q2]
    ring
  · intro t ht ξ
    have htd : 0 < t ^ DExp p := Real.rpow_pos_of_pos ht _
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      simp [ExtremalH]
    · have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hnorm : ‖((t ^ DExp p : ℝ) : ℂ) * ξ‖ = t ^ DExp p * ‖ξ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htd.le]
      have hpow : (t ^ DExp p * ‖ξ‖) ^ (1 / DExp p) = t * ‖ξ‖ ^ (1 / DExp p) := by
        rw [Real.mul_rpow htd.le hξn.le, ← Real.rpow_mul ht.le, mul_one_div,
          div_self hdpos.ne', Real.rpow_one]
      unfold ExtremalH
      rw [hnorm, hpow]
      push_cast
      have hξ3 : ξ ^ 3 ≠ 0 := pow_ne_zero _ hξ
      have hnξ : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by simpa using hξn.ne'
      have htdC : ((t ^ DExp p : ℝ) : ℂ) ≠ 0 := by simpa using htd.ne'
      field_simp
