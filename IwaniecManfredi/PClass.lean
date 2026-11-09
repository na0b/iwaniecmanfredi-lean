import IwaniecManfredi.MonomialValue

/-- `PClass H s k P` says that `P` belongs to the class `ℙ(s,k)` of Section 5
of the paper, relative to `H`: `P` is, as a function on `ℂ`, a finite
`ℂ`-linear combination of monomials of type `(s,k)`.  Membership comes with a
witnessing presentation of `P` as such a combination, which is what the later
growth estimates are read off from. -/
def PClass (H : ℂ → ℂ) (s k : ℕ) (P : ℂ → ℂ) : Prop :=
  ∃ L : List (ℂ × List DerivSymbol),
    (∀ cm ∈ L, (cm.2.map (fun d => d.i + d.j)).sum = s ∧ cm.2.length = k) ∧
    ∀ ξ, P ξ = (L.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum
