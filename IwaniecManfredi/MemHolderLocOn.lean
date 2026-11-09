import IwaniecManfredi.Preamble

/-- `MemHolderLocOn k α Ω u` says that `u : ℂ → ℂ` belongs to the Hölder space
`C^{k,α}_loc(Ω)` of Section 1 of the paper: `u` is `C^k` on `Ω` and its
derivatives of order `k` are locally Hölder continuous with exponent `α`. -/
def MemHolderLocOn (k : ℕ) (α : ℝ) (Ω : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ (k : ℕ) u Ω ∧
    ∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ k u Ω x - iteratedFDerivWithin ℝ k u Ω y‖ ≤ C * ‖x - y‖ ^ α
