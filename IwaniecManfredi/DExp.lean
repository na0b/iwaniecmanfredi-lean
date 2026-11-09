import IwaniecManfredi.Preamble

/-- `DExp p` is the exponent `d = d(p)` of equation (50) of the paper,
`d = (1/6)(1 + 1/(p-1) + sqrt(1 + 14/(p-1) + 1/(p-1)^2))`.  The last
denominator is `(p-1)^2`, following the transcription's correction of the
scan's `(p-2)^2`. -/
noncomputable def DExp (p : ℝ) : ℝ :=
  (1 + 1 / (p - 1) + Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2)) / 6
