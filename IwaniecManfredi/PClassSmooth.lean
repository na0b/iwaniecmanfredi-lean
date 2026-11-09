import IwaniecManfredi.PClass
import IwaniecManfredi.WirtingerIterSwap

/-- A member of `ℙ(s,k)` is `C^∞` on any open set where `H` is `C^∞`: it is a
finite linear combination of products of iterated Wirtinger derivatives of `H`
and their conjugates.  This is what licenses differentiating the `P` of
Lemma 1 and the Jacobian `J` inside the inductive step. -/
theorem PClassSmooth (H : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) (s k : ℕ) (P : ℂ → ℂ) (hP : PClass H s k P) :
    ContDiffOn ℝ (⊤ : ℕ∞) P Ω := by
  obtain ⟨L, hdeg, hval⟩ := hP
  have hsym : ∀ d : DerivSymbol, ContDiffOn ℝ (⊤ : ℕ∞) (SymbolValue H d) Ω := by
    intro d
    have hit : ContDiffOn ℝ (⊤ : ℕ∞) (WirtingerIter d.i d.j H) Ω :=
      (WirtingerIterSwap H Ω hΩ hH d.i d.j).1
    unfold SymbolValue
    by_cases hc : d.conjugated
    · simp only [hc, if_true]
      exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hit
    · simp only [hc]
      exact hit
  have hmon : ∀ M : List DerivSymbol, ContDiffOn ℝ (⊤ : ℕ∞) (MonomialValue H M) Ω := by
    intro M
    unfold MonomialValue
    induction M with
    | nil => simpa using contDiffOn_const
    | cons d tl ih => simpa using (hsym d).mul ih
  have hsum : ∀ A : List (ℂ × List DerivSymbol),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => (A.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum) Ω := by
    intro A
    induction A with
    | nil => simpa using contDiffOn_const
    | cons cm tl ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (contDiffOn_const.mul (hmon cm.2)).add ih
  have hPeq : P = fun ξ => (L.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum := funext hval
  rw [hPeq]
  exact hsum L
