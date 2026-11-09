import IwaniecManfredi.Preamble

/-- The polar angular derivative `H_θ` of Section 4 of the paper, as a function
of `ξ`: the real directional derivative of `H` at `ξ` along `iξ`.  At
`ξ = r e^{iθ}` that vector is `i r e^{iθ} = ∂(r e^{iθ})/∂θ`, so `HAng H ξ` is
exactly `∂H(r,θ)/∂θ`. -/
noncomputable def HAng (H : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  fderiv ℝ H ξ (Complex.I * ξ)
