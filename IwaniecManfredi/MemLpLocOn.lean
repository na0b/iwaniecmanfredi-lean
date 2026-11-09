import IwaniecManfredi.Preamble

open MeasureTheory

/-- `MemLpLocOn s Ω u` says that `u : ℂ → ℂ` belongs to `L^s_loc(Ω)`: the
restriction of `u` to every compact subset of `Ω` is `s`-integrable for plane
Lebesgue measure. -/
def MemLpLocOn (s : ENNReal) (Ω : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → MemLp (K.indicator u) s volume
