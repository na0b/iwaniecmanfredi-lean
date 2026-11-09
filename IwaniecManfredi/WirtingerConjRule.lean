import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar
import Mathlib.Analysis.Calculus.FDeriv.Star

/-- The conjugation rule for the Wirtinger operators: for `f`
real-differentiable at `ξ`, `∂(conj f)/∂ξ = conj(f_ξ̄)` and
`∂(conj f)/∂ξ̄ = conj(f_ξ)`.  This is what lets a conjugated factor be
differentiated without leaving the class of conjugated partials. -/
theorem WirtingerConjRule (f : ℂ → ℂ) (ξ : ℂ) (hf : DifferentiableAt ℝ f ξ) :
    DZ (fun z => starRingEnd ℂ (f z)) ξ = starRingEnd ℂ (DZbar f ξ) ∧
      DZbar (fun z => starRingEnd ℂ (f z)) ξ = starRingEnd ℂ (DZ f ξ) := by
  have hd : ∀ v : ℂ, fderiv ℝ (fun z => starRingEnd ℂ (f z)) ξ v
      = starRingEnd ℂ (fderiv ℝ f ξ v) := by
    intro v
    have hfun : (fun z => starRingEnd ℂ (f z)) = (fun z => star (f z)) := rfl
    rw [hfun, fderiv_star]
    rfl
  refine ⟨?_, ?_⟩
  · rw [DZ, DZbar, hd, hd]
    simp only [map_mul, map_add, Complex.conj_I, map_div₀, map_one, map_ofNat]
    ring
  · rw [DZbar, DZ, hd, hd]
    simp only [map_mul, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
    ring
