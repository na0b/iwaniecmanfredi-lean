import IwaniecManfredi.Preamble

/-- The Wirtinger operator `∂/∂z = (1/2)(∂/∂x - i ∂/∂y)` of Section 2 of the
paper, applied to a map `f : ℂ → ℂ` and evaluated through the real Fréchet
derivative: `∂f/∂z (z) = (1/2)(Df(z)[1] - i Df(z)[i])`. -/
noncomputable def DZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)
