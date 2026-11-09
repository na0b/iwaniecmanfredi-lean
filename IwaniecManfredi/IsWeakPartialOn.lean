import IwaniecManfredi.IsTestFn

/-- `IsWeakPartialOn Ω j u v` says that `v` is the distributional partial
derivative `∂u/∂x_j` of `u` on `Ω`, where `x_0 = x` and `x_1 = y` under the
identification `z = x + i y`: the integration-by-parts identity
`∫ u ∂_j φ = -∫ v φ` holds for every test function `φ` for `Ω`. -/
def IsWeakPartialOn (Ω : Set ℂ) (j : Fin 2) (u v : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, IsTestFn Ω φ →
    (∫ z, u z * fderiv ℝ φ z (if j = 0 then 1 else Complex.I)) = -∫ z, v z * φ z
