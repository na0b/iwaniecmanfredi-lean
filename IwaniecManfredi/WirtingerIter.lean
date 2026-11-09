import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar

/-- The iterated Wirtinger derivative `∂^{i+j}H / ∂ξ^i ∂ξ̄^j`, obtained by
applying `∂/∂ξ̄` to `H` `j` times and then `∂/∂ξ` `i` times.  These are the
partials `∂^s H / ∂ξ^i ∂ξ̄^j`, `s = i + j`, of the convention of Section 5 of
the paper. -/
noncomputable def WirtingerIter (i j : ℕ) (H : ℂ → ℂ) : ℂ → ℂ :=
  DZ^[i] (DZbar^[j] H)
