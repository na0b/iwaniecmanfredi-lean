import IwaniecManfredi.WirtingerProductRule
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Comp

/-- The power rule for the Wirtinger operators at an arbitrary integer
exponent: on an open set where `g` is `C^∞` and non-vanishing,
`∂(g^a)/∂ξ = a g^{a-1} g_ξ` and likewise for `∂/∂ξ̄`.  This is what turns
`J^{1-2m}` into the factor `(1-2m) J^{-2m} J_ξ` in the inductive step of
Lemma 1, and it will be needed again for the `J^{1-2l}` of Corollary 2. -/
theorem WirtingerPowerRule (g : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (hgne : ∀ ζ ∈ Ω, g ζ ≠ 0) (a : ℤ) :
    ∀ ξ ∈ Ω, DZ (fun z => g z ^ a) ξ = (a : ℂ) * g ξ ^ (a - 1) * DZ g ξ ∧
      DZbar (fun z => g z ^ a) ξ = (a : ℂ) * g ξ ^ (a - 1) * DZbar g ξ := by
  intro ξ hξ
  have hne : g ξ ≠ 0 := hgne ξ hξ
  have hgd : DifferentiableAt ℝ g ξ :=
    (hg.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ)
  have hout : HasDerivAt (fun w : ℂ => w ^ a) ((a : ℂ) * g ξ ^ (a - 1)) (g ξ) :=
    hasDerivAt_zpow a (g ξ) (Or.inl hne)
  have hcomp : HasFDerivAt (fun z => g z ^ a)
      (((a : ℂ) * g ξ ^ (a - 1)) • fderiv ℝ g ξ) ξ :=
    hout.comp_hasFDerivAt ξ hgd.hasFDerivAt
  have hd : ∀ v : ℂ, fderiv ℝ (fun z => g z ^ a) ξ v
      = (a : ℂ) * g ξ ^ (a - 1) * fderiv ℝ g ξ v := by
    intro v
    rw [hcomp.fderiv]
    simp [smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [DZ, DZ, hd, hd]; ring
  · rw [DZbar, DZbar, hd, hd]; ring
