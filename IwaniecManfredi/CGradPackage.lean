import IwaniecManfredi.PHarmonicOn
import IwaniecManfredi.SolvesEq12
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.QuasiregularOn

/-- The hypothesis bundle (C1) of the paper's note for the formalization: the
results of [BI], [Ma] quoted without proof, namely that the complex gradient
`f = ∂u/∂z` of a `p`-harmonic `u ∈ W^{1,p}_loc(Ω)` lies in `W^{1,2}_loc(Ω)`,
satisfies (12) a.e., and is `K`-quasiregular with `K` as in (13).  Per
`paper/paper.tex:103` this is carried as an explicit hypothesis, never as an
axiom.

The second clause reads the same quoted sentence for a *continuous
representative* of the complex gradient.  Its equation clause is not a
strengthening: `SolvesEq12` is an identity between the *weak* Wirtinger
derivatives of its argument, which depend only on that argument's
almost-everywhere class, so `SolvesEq12 p Ω fc` and `SolvesEq12 p Ω f` are
equivalent once `fc = f` a.e. on `Ω`; the clause is recorded to spare the
consumer that unfolding, and it is about the right object, since the paper's
complex gradient is the continuous one (`paper.tex:156` says in as many words
that `f = ∂u/∂z` is continuous and writes its zero set as
`f⁻¹(0) = {z : ∇u(z) = 0}`).  The one item not contained in the quoted
sentence is almost-everywhere differentiability of the representative, which
is the standard a.e. differentiability of a quasiregular mapping, quoted from
the same sources; it is carried rather than proved because it is an *input* to
the bundle (C3) and is not among the conclusions (C2) quotes.  The
representative itself is supplied by the consumer, which gets it from (C2). -/
structure CGradPackage where
  complex_gradient :
    ∀ (p : ℝ) (Ω : Set ℂ) (u : ℂ → ℝ) (g : ℂ → ℂ), IsOpen Ω → 1 < p →
      PHarmonicOn p Ω u →
      IsWeakPartialOn Ω 0 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).re : ℝ) : ℂ)) →
      IsWeakPartialOn Ω 1 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).im : ℝ) : ℂ)) →
      MemWLocOn 1 2 Ω (fun z => (1 / 2 : ℂ) * starRingEnd ℂ (g z)) ∧
      SolvesEq12 p Ω (fun z => (1 / 2 : ℂ) * starRingEnd ℂ (g z)) ∧
      QuasiregularOn (max (p - 1) (1 / (p - 1))) Ω
        (fun z => (1 / 2 : ℂ) * starRingEnd ℂ (g z))
  complex_gradient_rep :
    ∀ (p : ℝ) (Ω : Set ℂ) (u : ℂ → ℝ) (g fc : ℂ → ℂ), IsOpen Ω → 1 < p →
      PHarmonicOn p Ω u →
      IsWeakPartialOn Ω 0 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).re : ℝ) : ℂ)) →
      IsWeakPartialOn Ω 1 (fun z => ((u z : ℝ) : ℂ)) (fun z => (((g z).im : ℝ) : ℂ)) →
      (∀ᵐ z : ℂ, z ∈ Ω → fc z = (1 / 2 : ℂ) * starRingEnd ℂ (g z)) →
      ContinuousOn fc Ω →
      (∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ fc z) ∧ SolvesEq12 p Ω fc
