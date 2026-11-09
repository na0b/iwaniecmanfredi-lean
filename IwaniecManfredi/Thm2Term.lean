import IwaniecManfredi.EpsCoef

/-- The `k`-th summand of the series (19) of Theorem 2 of the paper:
`(A_k ξ^k + ε_k conj(A_k) conj(ξ)^k) |ξ|^{λ_k + n - k} ξ^{-n}`. -/
noncomputable def Thm2Term (n : ℕ) (p : ℝ) (A : ℤ → ℂ) (k : ℕ) (ξ : ℂ) : ℂ :=
  (A (k : ℤ) * ξ ^ k
      + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)
    * ((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * ξ ^ (-(n : ℤ))
