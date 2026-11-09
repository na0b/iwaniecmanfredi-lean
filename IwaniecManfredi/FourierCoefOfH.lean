import IwaniecManfredi.Preamble
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-- The Fourier coefficient (30) of the paper:
`a_k(r) = (1/2π) ∫₀^{2π} H(r e^{iθ}) e^{i(n-k)θ} dθ` for `k ∈ ℤ`.  The scan
prints the upper limit of (30) as `2k`; it is `2π`. -/
noncomputable def FourierCoefOfH (n : ℕ) (H : ℂ → ℂ) (k : ℤ) (r : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      * Complex.exp ((((n : ℤ) - k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
