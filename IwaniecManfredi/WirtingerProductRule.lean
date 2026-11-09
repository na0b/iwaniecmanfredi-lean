import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar

/-- The Leibniz rule for the Wirtinger operators: for `f`, `g`
real-differentiable at `ξ`, `∂(fg)/∂ξ = f_ξ g + f g_ξ` and
`∂(fg)/∂ξ̄ = f_ξ̄ g + f g_ξ̄`. -/
theorem WirtingerProductRule (f g : ℂ → ℂ) (ξ : ℂ)
    (hf : DifferentiableAt ℝ f ξ) (hg : DifferentiableAt ℝ g ξ) :
    DZ (fun z => f z * g z) ξ = DZ f ξ * g ξ + f ξ * DZ g ξ ∧
      DZbar (fun z => f z * g z) ξ = DZbar f ξ * g ξ + f ξ * DZbar g ξ := by
  have h : HasFDerivAt (fun z => f z * g z)
      (f ξ • fderiv ℝ g ξ + g ξ • fderiv ℝ f ξ) ξ :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  have hd : ∀ v : ℂ, fderiv ℝ (fun z => f z * g z) ξ v
      = fderiv ℝ f ξ v * g ξ + f ξ * fderiv ℝ g ξ v := by
    intro v
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [DZ, DZ, DZ, hd, hd]; ring
  · rw [DZbar, DZbar, DZbar, hd, hd]; ring
