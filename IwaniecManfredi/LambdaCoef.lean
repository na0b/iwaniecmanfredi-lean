import IwaniecManfredi.Preamble

/-- `LambdaCoef n k p` is the exponent `λ_k(n,p)` of equation (20) (equivalently
(37)) of the paper:
`λ_k(n,p) = (1/2)(-n p + sqrt(4 k^2 (p-1) + n^2 (p-2)^2))`. -/
noncomputable def LambdaCoef (n k : ℕ) (p : ℝ) : ℝ :=
  (-(n : ℝ) * p + Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2)) / 2
