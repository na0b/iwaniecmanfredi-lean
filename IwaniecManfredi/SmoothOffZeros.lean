import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.SolvesEq12

/-- The hypothesis bundle (C3) of the paper's note for the formalization: the
elliptic-regularity result used in Section 2, that a `W^{1,2}_loc` solution of
(12) is `C^∞` outside its zero set.  Per `paper/paper.tex:103` this is carried
as an explicit hypothesis, never as an axiom.

The conclusion is asserted of a *representative* `g`, and the zero set is
`g⁻¹(0)`.  It has to be: `MemWLocOn` and `SolvesEq12` both see the function
only almost everywhere -- the first through integrals, the second because it
is an identity between the *weak* Wirtinger derivatives, which depend only on
the almost-everywhere class -- so smoothness of `f` itself at any point is not
implied, and the set `f⁻¹(0)` is not determined modulo null sets.  The paper
writes the exceptional set as `f⁻¹(0) = {z : ∇u(z) = 0}` (`paper.tex:156`),
that is, as the zero set of the continuous complex gradient, which is exactly
`g⁻¹(0)` here.  The two hypotheses that pin `g` down -- continuity and
almost-everywhere differentiability -- only weaken the bundle, so it remains
no stronger than the quoted statement; and almost-everywhere differentiability
is what makes the *classical* Wirtinger derivatives of `g`, the objects the
elliptic theory differentiates, satisfy (12) almost everywhere as well. -/
structure SmoothOffZeros where
  smooth_off_zeros :
    ∀ (p : ℝ) (Ω : Set ℂ) (f g : ℂ → ℂ), IsOpen Ω → 1 < p →
      MemWLocOn 1 2 Ω f →
      (∀ᵐ z : ℂ, z ∈ Ω → g z = f z) → ContinuousOn g Ω →
      (∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ g z) →
      SolvesEq12 p Ω g →
      ContDiffOn ℝ (⊤ : ℕ∞) g (Ω \ {z | g z = 0})
