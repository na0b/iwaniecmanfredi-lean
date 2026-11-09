import IwaniecManfredi.Preamble
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-- The index (winding number) about `0` of a continuous **path** `γ` in
`ℂ - {0}` -- no loop condition is imposed -- defined by lifting its argument
along the covering map `ℝ → AddCircle (2π)`: the lift starts at `arg (γ 0)` and
the index is `(lift 1 - lift 0) / 2π`, the normalised argument increment.  It
is an integer exactly when `γ` is a loop.  This is the quantity behind the
paper's step at `paper.tex:382` ("Applying argument principle"). -/
noncomputable def WindingNumber (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0) : ℝ :=
  ((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
      ⟨fun t => ((Complex.arg (γ t) : ℝ) : Real.Angle), by
        refine continuous_iff_continuousAt.2 fun t => ?_
        exact (Complex.continuousAt_arg_coe_angle (hne t)).comp γ.continuous.continuousAt⟩
      (Complex.arg (γ 0)) rfl 1
    - Complex.arg (γ 0)) / (2 * Real.pi)
