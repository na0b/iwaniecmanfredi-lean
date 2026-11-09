import IwaniecManfredi.LambdaCoef

/-- `GammaExp n p` is the exponent `γ_n = λ_{n+1}(n,p)` of equation (44) of the
paper. -/
noncomputable def GammaExp (n : ℕ) (p : ℝ) : ℝ :=
  LambdaCoef n (n + 1) p
