import IwaniecManfredi.Preamble

/-- `KAlphaExp p` is the right-hand side of equation (9) of the paper, the
number that the pair `(k, α)` of Theorem 1 is required to add up to:
`(1/6)(7 + 1/(p-1) + sqrt(1 + 14/(p-1) + 1/(p-1)^2))`. -/
noncomputable def KAlphaExp (p : ℝ) : ℝ :=
  (7 + 1 / (p - 1) + Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2)) / 6
