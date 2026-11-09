import IwaniecManfredi.MemHolderLocOn
import IwaniecManfredi.Preamble

/-- `MemHolderSmallOn k α Ω u` says that `u : ℂ → ℂ` belongs to the space
`C^{k+α}_loc(Ω)` of Section 1 of the paper.  For `0 < α < 1` this is the
little-o condition that Section 1 gives as the characterization of
`C^{k+α}_loc(Ω)`; for `α = 1` the space coincides with `C^{k+1}(Ω)`. -/
def MemHolderSmallOn (k : ℕ) (α : ℝ) (Ω : Set ℂ) (u : ℂ → ℂ) : Prop :=
  (α = 1 ∧ ContDiffOn ℝ ((k : ℕ) + 1) u Ω) ∨
  (α < 1 ∧ ContDiffOn ℝ (k : ℕ) u Ω ∧
    ∀ K ⊆ Ω, IsCompact K → ∀ δ > 0, ∃ ρ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < ρ →
      ‖iteratedFDerivWithin ℝ k u Ω x - iteratedFDerivWithin ℝ k u Ω y‖ ≤ δ * ‖x - y‖ ^ α)
