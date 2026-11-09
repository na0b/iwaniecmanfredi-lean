import IwaniecManfredi.IsWeakWirtingerOn

/-- `SolvesEq12 p Ω f` says that `f : ℂ → ℂ` satisfies the complex form (12) of
the `p`-harmonic equation almost everywhere on `Ω`, away from the zeros of `f`:
`f_z̄ = (1/p - 1/2)[(f̄/f) f_z + (f/f̄) conj(f_z)]`, the derivatives being the
*weak* Wirtinger derivatives of `f`.

Equation (12) is the paper's one complex equation for the complex gradient
`f = ∂u/∂z` of a `p`-harmonic `u`, and it is stated in the same breath as the
distortion inequality (11), about the same `f`, whose only hypothesis there is
`f ∈ W^{1,2}_loc(Ω)`; so its derivatives are the distributional ones, exactly
as in `QuasiregularOn`.  Read through `fderiv ℝ` of the given representative
the equation would be satisfied vacuously by every nowhere differentiable
representative of an `L²`-class, both sides being `0`.  The pointwise form,
which the elliptic-regularity and hodograph steps consume, follows on the
almost everywhere differentiable maps those steps are about. -/
def SolvesEq12 (p : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ a b : ℂ → ℂ, IsWeakWirtingerOn Ω f a b ∧
    ∀ᵐ z, z ∈ Ω → f z ≠ 0 →
      b z = ((1 / p - 1 / 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ (f z) / f z) * a z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (a z))
