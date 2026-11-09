import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.IsWeakPartialOn

/-- `PHarmonicOn p Ω u` says that the real-valued function `u : ℂ → ℝ` is
`p`-harmonic on the plane domain `Ω` in the sense of Section 1 of the paper:
`u ∈ W^{1,p}_loc(Ω)` with weak gradient `g = u_x + i u_y`, and `u` is a weak
solution of `div(|∇u|^{p-2} ∇u) = 0`, i.e.
`∫ |∇u|^{p-2} ⟪∇u, ∇φ⟫ = 0` for every real test function `φ` for `Ω`. -/
def PHarmonicOn (p : ℝ) (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∃ g : ℂ → ℂ,
    MemLpLocOn (ENNReal.ofReal p) Ω (fun z => ((u z : ℝ) : ℂ)) ∧
    MemLpLocOn (ENNReal.ofReal p) Ω g ∧
    IsWeakPartialOn Ω 0 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).re : ℝ) : ℂ)) ∧
    IsWeakPartialOn Ω 1 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).im : ℝ) : ℂ)) ∧
    ∀ φ : ℂ → ℝ, IsTestFn Ω (fun z => ((φ z : ℝ) : ℂ)) →
      (∫ z, ‖g z‖ ^ (p - 2) *
          (g z * starRingEnd ℂ
            (((fderiv ℝ φ z 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ φ z Complex.I : ℝ) : ℂ))).re)
        = 0
