import IwaniecManfredi.LambdaCoef

/-- `EpsCoef n k p` is the coefficient `ε_k(n,p)` of equation (21) of the paper:
`ε_k(n,p) = (λ_k(n,p) + n - k) / (λ_k(n,p) + n + k)`. -/
noncomputable def EpsCoef (n k : ℕ) (p : ℝ) : ℝ :=
  (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / (LambdaCoef n k p + (n : ℝ) + (k : ℝ))
