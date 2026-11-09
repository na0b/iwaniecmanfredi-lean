import IwaniecManfredi.EpsCoef
import IwaniecManfredi.DExp

/-- The extremal function (54) of Section 7 of the paper,
`H(ξ) = (ξ/|ξ| + ε |ξ|³/ξ³) |ξ|^{1/d}` with `d = d(p)` and
`ε = ε₂(1,p)`, obtained from the series (19) by taking `n = 1` and
`A₁ = 0`, `A₂ = 1`, `A₃ = A₄ = ⋯ = 0`. -/
noncomputable def ExtremalH (p : ℝ) (ξ : ℂ) : ℂ :=
  (ξ / ((‖ξ‖ : ℝ) : ℂ) + ((EpsCoef 1 2 p : ℝ) : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3))
    * ((‖ξ‖ ^ (1 / DExp p) : ℝ) : ℂ)
