import IwaniecManfredi.Preamble

/-- `PartialWord w f` is the iterated real partial derivative
`∂_{j₁} ∂_{j₂} ⋯ ∂_{j_m} f` of `f : ℂ → ℂ` along the word `w = [j₁, …, j_m]`,
where `∂_0 = ∂/∂x` and `∂_1 = ∂/∂y` under the identification `z = x + i y`.
Words of length `m` realize exactly the operators `D^ν` with `|ν| = m` used
throughout the paper. -/
noncomputable def PartialWord (w : List (Fin 2)) (f : ℂ → ℂ) : ℂ → ℂ :=
  w.foldr (fun j g z => fderiv ℝ g z (if j = 0 then 1 else Complex.I)) f
