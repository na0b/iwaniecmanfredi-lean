import IwaniecManfredi.Preamble

/-- The polar radial derivative `H_r` of Section 4 of the paper, as a function
of `ξ`: the real directional derivative of `H` at `ξ` along the unit vector
`ξ/|ξ|`.  At `ξ = r e^{iθ}` with `r > 0` this unit vector is `e^{iθ} =
∂(r e^{iθ})/∂r`, so `HRad H ξ` is exactly `∂H(r,θ)/∂r`. -/
noncomputable def HRad (H : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  fderiv ℝ H ξ (ξ / ((‖ξ‖ : ℝ) : ℂ))
