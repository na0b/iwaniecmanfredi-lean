import IwaniecManfredi.SymbolValue

/-- The monomial determined by a finite list `M = [d₁, …, d_k]` of derivative
symbols: the pointwise product `H^{d₁} ⋯ H^{d_k}` of the symbol values.  Its
type `(s, k)` in the sense of Section 5 of the paper is computed from the list:
`k` is the length of `M` and `s` the sum of the orders of its entries. -/
noncomputable def MonomialValue (H : ℂ → ℂ) (M : List DerivSymbol) : ℂ → ℂ :=
  fun ξ => (M.map (fun d => SymbolValue H d ξ)).prod
