-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).

-- Differential calculus: real Frechet derivatives, iterated derivatives, C^k classes.
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue

-- Real powers and square roots (the exponents of Section 1 and formulas (9), (20), (50)).
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- The plane as the complex field, and R^n as a Euclidean space (Lemma 2).
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

-- Measure theory for the local Lebesgue/Sobolev spaces of Section 1.
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- Holder continuity and smooth bump functions (test functions).
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.BumpFunction.Normed

-- Ceiling/floor, used to split (9) into its integer and fractional parts.
import Mathlib.Algebra.Order.Floor.Defs

-- Mollification and convolution (the continuous representative of Section 6).
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

-- Passing to the limit in a locally uniformly convergent family of derivatives.
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

-- The plane divergence theorem with a countable exceptional set (the puncture),
-- and the extension of a derivative across the boundary of a convex set.
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Extend
