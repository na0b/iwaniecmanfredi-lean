import IwaniecManfredi.IsWeakPartialOn
import IwaniecManfredi.MemLpLocOn

/-- `IsWeakWirtingerOn Ω f a b` says that `a` and `b` are the *weak* Wirtinger
derivatives `∂f/∂z` and `∂f/∂z̄` of `f` on `Ω`: there are locally integrable
distributional first partial derivatives `fx = ∂f/∂x`, `fy = ∂f/∂y` of `f` on
`Ω`, and `a = (1/2)(fx - i fy)`, `b = (1/2)(fx + i fy)` are the combinations of
Section 2 of the paper.

This is the reading the paper's own text forces on the derivatives in (11),
(12) and (18).  At `paper.tex:129-133` a mapping is called `K`-quasiregular if
`f ∈ W^{1,2}_loc(Ω)` *and* (11) holds almost everywhere; at that point `f`
carries no hypothesis but Sobolev membership, so the only derivatives
available are the distributional ones whose existence that membership asserts.
The pointwise operators `DZ` and `DZbar`, which read the Fréchet derivative of
the given representative, are *not* a formalization of (11): they are built
from `fderiv ℝ`, which is `0` wherever the function fails to be
differentiable, so a nowhere-differentiable member of an `L^2`-class satisfies
any such inequality vacuously.  The two readings agree almost everywhere as
soon as the function is differentiable almost everywhere, which is what
`WeakPartialEqFDerivAE` supplies, and that is the only place where Sections
4-6 need the pointwise form.

Local integrability of `f`, `fx`, `fy` is part of the data: without it the
integration-by-parts identity of `IsWeakPartialOn` can be satisfied by
non-integrable junk, since a divergent Bochner integral is `0` by convention,
and it is also exactly hypothesis (H1) of `WeakPartialEqFDerivAE`. -/
def IsWeakWirtingerOn (Ω : Set ℂ) (f a b : ℂ → ℂ) : Prop :=
  ∃ fx fy : ℂ → ℂ,
    MemLpLocOn 1 Ω f ∧ MemLpLocOn 1 Ω fx ∧ MemLpLocOn 1 Ω fy ∧
    IsWeakPartialOn Ω 0 f fx ∧ IsWeakPartialOn Ω 1 f fy ∧
    (∀ z : ℂ, a z = (1 / 2 : ℂ) * (fx z - Complex.I * fy z)) ∧
    (∀ z : ℂ, b z = (1 / 2 : ℂ) * (fx z + Complex.I * fy z))
