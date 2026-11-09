import IwaniecManfredi.QuasiregularOn

/-- `QuasiconformalOn K Ω χ` says that `χ` is a `K`-quasiconformal
homeomorphism of the open set `Ω` onto its image: it is `K`-quasiregular on
`Ω` in the sense of Section 2 of the paper, and it maps `Ω` homeomorphically
onto the open set `χ(Ω)`. -/
def QuasiconformalOn (K : ℝ) (Ω : Set ℂ) (chi : ℂ → ℂ) : Prop :=
  QuasiregularOn K Ω chi ∧ Set.InjOn chi Ω ∧ ContinuousOn chi Ω ∧ IsOpen (chi '' Ω) ∧
    ∃ psi : ℂ → ℂ, (∀ z ∈ Ω, psi (chi z) = z) ∧ ContinuousOn psi (chi '' Ω)
