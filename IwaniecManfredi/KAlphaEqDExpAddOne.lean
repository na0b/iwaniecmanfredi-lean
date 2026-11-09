import IwaniecManfredi.KAlphaExp
import IwaniecManfredi.DExp

/-- The bridge `d = k - 1 + α` of `paper.tex:530`: the right-hand side of (9),
which the pair `(k, α)` of Theorem 1 adds up to, exceeds the exponent `d` of
(50) by exactly `1`.  The two formulas differ only in the `7` against the `1`,
and `7/6 - 1/6 = 1`.  Both halves of Theorem 1 need this: the regularity half
converts Corollary 2's exponent `d - m` into `k - 1 + α - m`, and the
optimality half reads the cases (58), (59) off the same identity. -/
theorem KAlphaEqDExpAddOne (p : ℝ) (hp : 1 < p) : KAlphaExp p = DExp p + 1 := by
  unfold KAlphaExp DExp
  ring
