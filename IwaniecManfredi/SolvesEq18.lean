import IwaniecManfredi.IsWeakWirtingerOn

/-- `SolvesEq18 n p Ω H` says that `H : ℂ → ℂ` satisfies the linear hodograph
system (18) of the paper almost everywhere on `Ω`, away from the origin:
`H_ξ̄ = (1/2 - 1/p)[(ξ/ξ̄) H_ξ + (ξ̄^n/ξ^n) conj(H_ξ)]`, the derivatives being
the *weak* Wirtinger derivatives of `H`.

The weak reading is forced for the same reason as in the definition of
quasiregularity: the paper's solutions of (18) are assumed only to lie in
`W^{1,2}`, so `H_ξ` and `H_ξ̄` are the distributional derivatives.  Read
through `fderiv ℝ` of the given representative the system would say nothing
about a nowhere differentiable representative of an `L²`-class, both sides
being `0` there, and the assertion that a `W^{1,2}` solution of (18) is
quasiregular would then be false.  Where a pointwise form of (18) is needed --
throughout Sections 4 to 6 -- it is recovered from this one on the
almost-everywhere differentiable maps those sections are about. -/
def SolvesEq18 (n : ℕ) (p : ℝ) (Ω : Set ℂ) (H : ℂ → ℂ) : Prop :=
  ∃ a b : ℂ → ℂ, IsWeakWirtingerOn Ω H a b ∧
    ∀ᵐ ξ, ξ ∈ Ω → ξ ≠ 0 →
      b ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * a ξ
          + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ (a ξ))
