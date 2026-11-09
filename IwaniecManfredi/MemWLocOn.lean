import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.IsWeakPartialOn

/-- `MemWLocOn k s Ω u` says that `u : ℂ → ℂ` belongs to the local Sobolev
space `W^{k,s}_loc(Ω)` of Section 1 of the paper: there is a coherent family
of distributional derivatives of `u` indexed by words of length at most `k` in
`{∂/∂x, ∂/∂y}`, all of which lie in `L^s_loc(Ω)`. -/
def MemWLocOn (k : ℕ) (s : ENNReal) (Ω : Set ℂ) (u : ℂ → ℂ) : Prop :=
  ∃ D : List (Fin 2) → (ℂ → ℂ),
    D [] = u ∧
    (∀ w : List (Fin 2), w.length ≤ k → MemLpLocOn s Ω (D w)) ∧
    (∀ (w : List (Fin 2)) (j : Fin 2), w.length < k →
      IsWeakPartialOn Ω j (D w) (D (w ++ [j])))
