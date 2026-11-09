import IwaniecManfredi.WirtingerIter
import IwaniecManfredi.DerivSymbol

/-- The value on `H` of a derivative symbol `d = (i, j, β)`: the iterated
Wirtinger derivative `∂^{i+j}H/∂ξ^i ∂ξ̄^j` when `β` is false, and its complex
conjugate when `β` is true.  This is one of the partials written `H^s` in
Section 5 of the paper, with `s = i + j`. -/
noncomputable def SymbolValue (H : ℂ → ℂ) (d : DerivSymbol) : ℂ → ℂ :=
  if d.conjugated then (fun ξ => starRingEnd ℂ (WirtingerIter d.i d.j H ξ))
  else WirtingerIter d.i d.j H
