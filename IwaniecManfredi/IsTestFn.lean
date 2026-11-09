import IwaniecManfredi.Preamble

/-- `IsTestFn Ω φ` says that `φ : ℂ → ℂ` is a test function for `Ω`: smooth on
the plane, with compact support contained in `Ω`.  This is the class
`C_c^∞(Ω)` against which the weak derivatives and the weak form of the
`p`-harmonic equation are tested. -/
def IsTestFn (Ω : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω
