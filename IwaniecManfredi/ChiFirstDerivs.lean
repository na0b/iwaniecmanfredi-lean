import IwaniecManfredi.Jac
import IwaniecManfredi.WirtingerChainRule

/-- Equations (17) and (46) of the paper: for a pair of mutually inverse maps,
the first-order Wirtinger derivatives of one are expressed through those of the
other, `χ_z = J^{-1} conj(H_ξ)` and `χ_z̄ = -J^{-1} H_ξ̄`.  The hypotheses
constrain the pair `(χ, H)` only through `χ ∘ H = id` near the point, so the
statement applies with the two roles exchanged as well, which is the direction
Section 7 needs. -/
theorem ChiFirstDerivs (U : Set ℂ) (hU : IsOpen U) (chi H : ℂ → ℂ) (ξ : ℂ) (hξ : ξ ∈ U)
    (hinv : ∀ ζ ∈ U, chi (H ζ) = ζ)
    (hH : DifferentiableAt ℝ H ξ) (hchi : DifferentiableAt ℝ chi (H ξ))
    (hJ : Jac H ξ ≠ 0) :
    DZ chi (H ξ) = starRingEnd ℂ (DZ H ξ) / ((Jac H ξ : ℝ) : ℂ) ∧
      DZbar chi (H ξ) = -(DZbar H ξ) / ((Jac H ξ : ℝ) : ℂ) := by
  -- ## Step 1: `chi ∘ H` agrees with the identity near `ξ`
  have hcomp : (fun z : ℂ => chi (H z)) =ᶠ[nhds ξ] (fun z : ℂ => z) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hξ) (fun z hz => hinv z hz)
  have hfd : fderiv ℝ (fun z : ℂ => chi (H z)) ξ = fderiv ℝ (fun z : ℂ => z) ξ :=
    hcomp.fderiv_eq
  have hDZ1 : DZ (fun z : ℂ => chi (H z)) ξ = 1 := by
    simp only [DZ, hfd, fderiv_fun_id, ContinuousLinearMap.id_apply, Complex.I_mul_I]
    ring
  have hDZb0 : DZbar (fun z : ℂ => chi (H z)) ξ = 0 := by
    simp only [DZbar, hfd, fderiv_fun_id, ContinuousLinearMap.id_apply, Complex.I_mul_I]
    ring
  -- ## Step 2: the chain rule gives the `2 × 2` system
  obtain ⟨hc1, hc2⟩ := WirtingerChainRule chi H ξ hH hchi
  rw [hDZ1] at hc1
  rw [hDZb0] at hc2
  obtain ⟨A, hA⟩ : ∃ x : ℂ, x = DZ H ξ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x : ℂ, x = DZbar H ξ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ x : ℂ, x = DZ chi (H ξ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x : ℂ, x = DZbar chi (H ξ) := ⟨_, rfl⟩
  rw [← hA, ← hB, ← ha, ← hb] at hc1 hc2
  have eq2 : a * A + b * starRingEnd ℂ B = 1 := hc1.symm
  have eq3 : a * B + b * starRingEnd ℂ A = 0 := hc2.symm
  -- ## Step 3: the determinant of the system is the Jacobian
  have hmc : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hdet : ((Jac H ξ : ℝ) : ℂ) = A * starRingEnd ℂ A - B * starRingEnd ℂ B := by
    rw [hmc A, hmc B]
    simp only [Jac, ← hA, ← hB]
    push_cast
    ring
  have hJc : ((Jac H ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hJ
  -- ## Steps 4 and 5: solve the system
  have h4 : a * ((Jac H ξ : ℝ) : ℂ) = starRingEnd ℂ A := by
    linear_combination (starRingEnd ℂ A) * eq2 - (starRingEnd ℂ B) * eq3 + a * hdet
  have h5 : b * ((Jac H ξ : ℝ) : ℂ) = -B := by
    linear_combination A * eq3 - B * eq2 + b * hdet
  refine ⟨?_, ?_⟩
  · rw [← ha, ← hA, eq_div_iff hJc]
    exact h4
  · rw [← hb, ← hB, eq_div_iff hJc]
    exact h5
