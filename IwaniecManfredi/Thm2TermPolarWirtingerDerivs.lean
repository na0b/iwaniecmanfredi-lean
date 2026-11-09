import IwaniecManfredi.Thm2TermWirtingerDerivs
set_option maxHeartbeats 1000000

/-- The polar form of the two Wirtinger derivatives of a single summand of the
series (19): at `ξ = r e^{iθ}` with `r > 0`, each derivative is `r^{λ_k - 1}`
times a pair of pure angular exponentials with explicit complex coefficients,

`T_k,ξ (r e^{iθ}) = r^{λ_k-1} ( ((λ_k+k-n)/2) A_k e^{i(k-n-1)θ}`
`                             + ((λ_k-k-n)/2) ε_k conj(A_k) e^{i(-k-n-1)θ} )`,
`T_k,ξ̄(r e^{iθ}) = r^{λ_k-1} ( ((λ_k+n-k)/2) A_k e^{i(k-n+1)θ}`
`                             + ((λ_k+n+k)/2) ε_k conj(A_k) e^{i(-k-n+1)θ} )`.

This is the summand-level instance of the polar transformation formulas that
open Section 4 of the paper at `paper.tex:234-237`,
`H_ξ̄ = ½(H_r + (i/r)H_θ)e^{iθ}` and `H_ξ = ½(H_r - (i/r)H_θ)e^{-iθ}`: it is
what separates the radial from the angular dependence, and so it is the form
in which the two derivatives enter the circlewise Parseval computation and the
energy integral.

It follows from the Cartesian closed form of `Thm2TermWirtingerDerivs` by
substituting `ξ = r e^{iθ}`, using `|r e^{iθ}| = r` to collect the three
separate powers of the modulus into the single exponent `λ_k - 1`, and
`conj(e^{iθ}) = e^{-iθ}` to turn each product of powers of `e^{iθ}` and of its
conjugate into one exponential of an integer multiple of `θ`.

As for `Thm2TermWirtingerDerivs`, no inequality among `n`, `p` and `k` is
needed; the only hypothesis is `r > 0`, which keeps the point off the
origin. -/
theorem Thm2TermPolarWirtingerDerivs (n : ℕ) (p : ℝ) (A : ℤ → ℂ) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (θ : ℝ) :
    DZ (Thm2Term n p A k) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((r ^ (LambdaCoef n k p - 1) : ℝ) : ℂ)
        * ((((LambdaCoef n k p + (k : ℝ) - (n : ℝ)) / 2 : ℝ) : ℂ) * A (k : ℤ)
              * Complex.exp (((((k : ℤ) - (n : ℤ) - 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I)
          + (((LambdaCoef n k p - (k : ℝ) - (n : ℝ)) / 2 : ℝ) : ℂ)
              * ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * Complex.exp (((((-(k : ℤ)) - (n : ℤ) - 1 : ℤ)) : ℂ)
                  * (θ : ℂ) * Complex.I))
  ∧ DZbar (Thm2Term n p A k) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((r ^ (LambdaCoef n k p - 1) : ℝ) : ℂ)
        * ((((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 : ℝ) : ℂ) * A (k : ℤ)
              * Complex.exp (((((k : ℤ) - (n : ℤ) + 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I)
          + (((LambdaCoef n k p + (n : ℝ) + (k : ℝ)) / 2 : ℝ) : ℂ)
              * ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * Complex.exp (((((-(k : ℤ)) - (n : ℤ) + 1 : ℤ)) : ℂ)
                  * (θ : ℂ) * Complex.I)) := by
  -- the point `r e^{iθ}` is off the origin and has modulus `r`
  have hcirc : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) (Complex.exp_ne_zero _)
  have hcircnorm : ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hconjE : ∀ θ : ℝ, starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    intro θ
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  have hconjxi : ∀ (r : ℝ) (θ : ℝ),
      starRingEnd ℂ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (r : ℂ) * starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro r θ
    rw [map_mul, Complex.conj_ofReal]
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hEne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hxi := hcirc
  have hyne : starRingEnd ℂ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
    simpa using hxi
  have hEcne : starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
    rw [hconjE θ]
    exact Complex.exp_ne_zero _
  have hw := Thm2TermWirtingerDerivs n p A k _ hxi
  have hnrm := hcircnorm
  -- the radial identity
  have hRa : ((r : ℂ)) ^ k * ((r : ℂ)) ^ (-(n : ℤ))
        * ((r ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ) / (r : ℂ)
      = ((r ^ (LambdaCoef n k p - 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_zpow, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    rw [← Real.rpow_natCast r k, ← Real.rpow_intCast r (-(n : ℤ)),
      ← Real.rpow_add hr, ← Real.rpow_add hr, div_eq_mul_inv,
      ← Real.rpow_neg_one r, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hTa : Complex.exp ((θ : ℂ) * Complex.I) ^ k
        * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        / Complex.exp ((θ : ℂ) * Complex.I)
      = Complex.exp (((((k : ℤ) - (n : ℤ) - 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add,
      ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hTb : (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ k
        * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        / Complex.exp ((θ : ℂ) * Complex.I)
      = Complex.exp (((((-(k : ℤ)) - (n : ℤ) - 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I) := by
    rw [hconjE θ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add,
      ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hTc : Complex.exp ((θ : ℂ) * Complex.I) ^ k
        * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        / starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((((k : ℤ) - (n : ℤ) + 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I) := by
    rw [hconjE θ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add,
      ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  have hTd : (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ k
        * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        / starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((((-(k : ℤ)) - (n : ℤ) + 1 : ℤ)) : ℂ) * (θ : ℂ) * Complex.I) := by
    rw [hconjE θ, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add,
      ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  constructor
  · rw [hw.1, hnrm, hconjxi r θ, mul_pow, mul_pow, mul_zpow, ← hRa, ← hTa, ← hTb]
    push_cast
    field_simp
    ring
  · rw [hw.2, hnrm, hconjxi r θ, mul_pow, mul_pow, mul_zpow, ← hRa, ← hTc, ← hTd]
    push_cast
    field_simp
    ring
