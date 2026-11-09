import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar

/-- The Jacobian determinant `J(ξ) = |H_ξ|² - |H_ξ̄|²` of a map `H : ℂ → ℂ`,
as in equations (17) and (42) of the paper. -/
noncomputable def Jac (H : ℂ → ℂ) (ξ : ℂ) : ℝ :=
  ‖DZ H ξ‖ ^ 2 - ‖DZbar H ξ‖ ^ 2
