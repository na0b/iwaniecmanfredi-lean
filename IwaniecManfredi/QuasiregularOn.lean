import IwaniecManfredi.IsWeakWirtingerOn
import IwaniecManfredi.MemWLocOn

/-- `QuasiregularOn K Ω f` says that `f : ℂ → ℂ` is `K`-quasiregular on `Ω` in
the sense of Section 2 of the paper (`paper.tex:129-133`): `1 ≤ K < ∞`,
`f ∈ W^{1,2}_loc(Ω)`, and the distortion inequality (11)
`|f_z̄| ≤ ((K-1)/(K+1)) |f_z|` holds almost everywhere on `Ω`, the two
derivatives being the *weak* Wirtinger derivatives of `f`.

The weak reading is the paper's own: where (11) is stated, `f` has no
hypothesis but `f ∈ W^{1,2}_loc(Ω)`, so the derivatives in it are the
distributional ones whose existence that membership asserts.  Reading them
instead through `fderiv ℝ` of the given representative would make the
predicate vacuous on the many representatives that are nowhere
differentiable: `fderiv` is `0` where a function is not differentiable, so for
such an `f` the inequality would read `0 ≤ 0` at every point while `f` ranges
over the whole `L²`-class.  That is not a formalization of (11), and it makes
hypothesis bundles which quote the continuity of a quasiregular map
uninhabited.  Since the weak first derivatives of `f` are unique almost
everywhere on an open set, the choice of the witnessing pair `a`, `b` does not
matter. -/
def QuasiregularOn (K : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  1 ≤ K ∧ MemWLocOn 1 2 Ω f ∧
    ∃ a b : ℂ → ℂ, IsWeakWirtingerOn Ω f a b ∧
      ∀ᵐ z, z ∈ Ω → ‖b z‖ ≤ ((K - 1) / (K + 1)) * ‖a z‖
