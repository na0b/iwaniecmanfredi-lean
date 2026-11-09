import IwaniecManfredi.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-- The one-line integrability the paper leans on at `paper.tex:534`: the
function `|z|^{α-2}` is `L^q` on a disk about the origin for every exponent
`q` in the range (10), `1 ≤ q < 2/(2-α)`.  In polar coordinates the integral is
`2π ∫_0^δ r^{(α-2)q+1} dr`, and `(α-2)q + 1 > -1` is exactly
`q < 2/(2-α)`.  This is what turns the bound (52) at `m = k+1` into
`u ∈ W^{k+2,q}_loc`. -/
theorem PowerIntegrableNearZero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (q : ℝ) (hq : 1 ≤ q) (hq2 : q < 2 / (2 - α)) :
    MeasureTheory.IntegrableOn (fun z : ℂ => ‖z‖ ^ ((α - 2) * q))
      (Metric.ball (0 : ℂ) δ) MeasureTheory.volume := by
  have h2a : (0:ℝ) < 2 - α := by linarith
  have hqlt : (2 - α) * q < 2 := by
    rw [lt_div_iff₀ h2a] at hq2; linarith [hq2]
  have hexp : -((2 - α) * q) = (α - 2) * q := by ring
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ)
    (C := 1) (α := (2 - α) * q) (r := δ)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith) ?_ ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hexp, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), one_mul]
  · -- `fun z => ‖z‖ ^ e` agrees with `exp (log ‖z‖ * e)` off the null set `{0}`;
    -- `fun_prop` cannot do it directly because the exponent `e` may be negative.
    have hmeas : Measurable fun z : ℂ => Real.exp (Real.log ‖z‖ * ((α - 2) * q)) :=
      ((Real.measurable_log.comp measurable_norm).mul_const _).exp
    refine hmeas.aestronglyMeasurable.congr ?_
    have hnull : MeasureTheory.volume ({(0 : ℂ)} : Set ℂ) = 0 := by simp
    have hae : ∀ᵐ z : ℂ ∂MeasureTheory.volume, z ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hae] with z hz
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
