import IwaniecManfredi.Preamble

/-- A derivative symbol: the formal name of one factor `H^s` in the convention
of Section 5 of the paper.  It records the two differentiation orders `i`, `j`
and a Boolean saying whether the partial is conjugated; its order is
`i + j = s`, required to be positive.  Keeping `i`, `j` and the conjugation
flag as data is what makes the order of each individual factor of a monomial
recoverable from the monomial. -/
structure DerivSymbol where
  i : ℕ
  j : ℕ
  conjugated : Bool
  order_pos : 0 < i + j
