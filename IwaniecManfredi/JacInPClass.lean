import IwaniecManfredi.PClass
import IwaniecManfredi.Jac
import IwaniecManfredi.WirtingerProductRule
import IwaniecManfredi.WirtingerConjRule
import IwaniecManfredi.WirtingerIterSwap

/-- Property (ii) of Section 5 of the paper, together with the remark
preceding it: the Jacobian `J = H_ξ conj(H_ξ) - H_ξ̄ conj(H_ξ̄)` lies in
`ℙ(2,2)`, its `ξ`-derivative is the displayed four-term expression, and that
expression lies in `ℙ(3,2)`. -/
theorem JacInPClass (H : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) :
    PClass H 2 2 (fun ξ => ((Jac H ξ : ℝ) : ℂ)) ∧
    PClass H 3 2 (fun ξ =>
      WirtingerIter 2 0 H ξ * starRingEnd ℂ (WirtingerIter 1 0 H ξ)
      + starRingEnd ℂ (WirtingerIter 1 1 H ξ) * WirtingerIter 1 0 H ξ
      - WirtingerIter 1 1 H ξ * starRingEnd ℂ (WirtingerIter 0 1 H ξ)
      - starRingEnd ℂ (WirtingerIter 0 2 H ξ) * WirtingerIter 0 1 H ξ) ∧
    ∀ ξ ∈ Ω, DZ (fun ζ => ((Jac H ζ : ℝ) : ℂ)) ξ =
      WirtingerIter 2 0 H ξ * starRingEnd ℂ (WirtingerIter 1 0 H ξ)
      + starRingEnd ℂ (WirtingerIter 1 1 H ξ) * WirtingerIter 1 0 H ξ
      - WirtingerIter 1 1 H ξ * starRingEnd ℂ (WirtingerIter 0 1 H ξ)
      - starRingEnd ℂ (WirtingerIter 0 2 H ξ) * WirtingerIter 0 1 H ξ := by
  -- ## Step 1: the cast bridge, `J` as a difference of two products
  have hmc : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hW10 : WirtingerIter 1 0 H = DZ H := rfl
  have hW01 : WirtingerIter 0 1 H = DZbar H := rfl
  have hJval : ∀ ζ : ℂ, ((Jac H ζ : ℝ) : ℂ)
      = WirtingerIter 1 0 H ζ * starRingEnd ℂ (WirtingerIter 1 0 H ζ)
        - WirtingerIter 0 1 H ζ * starRingEnd ℂ (WirtingerIter 0 1 H ζ) := by
    intro ζ
    rw [hmc, hmc, hW10, hW01, Jac]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  -- ## Step 2: conjunct (a)
  · refine ⟨[((1 : ℂ), [(⟨1, 0, false, by omega⟩ : DerivSymbol),
        (⟨1, 0, true, by omega⟩ : DerivSymbol)]),
      ((-1 : ℂ), [(⟨0, 1, false, by omega⟩ : DerivSymbol),
        (⟨0, 1, true, by omega⟩ : DerivSymbol)])], ?_, ?_⟩
    · intro cm hcm
      fin_cases hcm <;> exact ⟨by simp, by simp⟩
    · intro ξ
      show ((Jac H ξ : ℝ) : ℂ) = _
      rw [hJval ξ]
      simp [MonomialValue, SymbolValue]
      ring
  -- ## Step 3: conjunct (b)
  · refine ⟨[((1 : ℂ), [(⟨2, 0, false, by omega⟩ : DerivSymbol),
        (⟨1, 0, true, by omega⟩ : DerivSymbol)]),
      ((1 : ℂ), [(⟨1, 1, true, by omega⟩ : DerivSymbol),
        (⟨1, 0, false, by omega⟩ : DerivSymbol)]),
      ((-1 : ℂ), [(⟨1, 1, false, by omega⟩ : DerivSymbol),
        (⟨0, 1, true, by omega⟩ : DerivSymbol)]),
      ((-1 : ℂ), [(⟨0, 2, true, by omega⟩ : DerivSymbol),
        (⟨0, 1, false, by omega⟩ : DerivSymbol)])], ?_, ?_⟩
    · intro cm hcm
      fin_cases hcm <;> exact ⟨by simp, by simp⟩
    · intro ξ
      simp [MonomialValue, SymbolValue]
      ring
  -- ## Steps 4, 5 and 6: conjunct (c)
  · intro ξ hξ
    -- the four first-order factors, named opaquely
    obtain ⟨A, hA⟩ : ∃ f : ℂ → ℂ, f = WirtingerIter 1 0 H := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ f : ℂ → ℂ, f = WirtingerIter 0 1 H := ⟨_, rfl⟩
    obtain ⟨Ac, hAc⟩ : ∃ f : ℂ → ℂ, f = fun z => starRingEnd ℂ (A z) := ⟨_, rfl⟩
    obtain ⟨Bc, hBc⟩ : ∃ f : ℂ → ℂ, f = fun z => starRingEnd ℂ (B z) := ⟨_, rfl⟩
    -- Step 4: differentiability
    have hdiff : ∀ (i j : ℕ), DifferentiableAt ℝ (WirtingerIter i j H) ξ := by
      intro i j
      exact (((WirtingerIterSwap H Ω hΩ hH i j).1).differentiableOn
        (by simp)).differentiableAt (hΩ.mem_nhds hξ)
    have hdA : DifferentiableAt ℝ A ξ := by rw [hA]; exact hdiff 1 0
    have hdB : DifferentiableAt ℝ B ξ := by rw [hB]; exact hdiff 0 1
    have hdAc : DifferentiableAt ℝ Ac ξ := by
      rw [hAc]
      exact (Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt).comp
        ξ hdA
    have hdBc : DifferentiableAt ℝ Bc ξ := by
      rw [hBc]
      exact (Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt).comp
        ξ hdB
    -- the four symbol derivatives: only `DZbar A` needs the commutation
    have hDZA : DZ A ξ = WirtingerIter 2 0 H ξ := by
      rw [hA]
      have he : WirtingerIter 2 0 H = DZ (WirtingerIter 1 0 H) := by
        rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
      rw [he]
    have hDZB : DZ B ξ = WirtingerIter 1 1 H ξ := by
      rw [hB]
      have he : WirtingerIter 1 1 H = DZ (WirtingerIter 0 1 H) := by
        rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
      rw [he]
    have hDZbarA : DZbar A ξ = WirtingerIter 1 1 H ξ := by
      rw [hA]
      exact (WirtingerIterSwap H Ω hΩ hH 1 0).2 ξ hξ
    have hDZbarB : DZbar B ξ = WirtingerIter 0 2 H ξ := by
      rw [hB]
      exact (WirtingerIterSwap H Ω hΩ hH 0 1).2 ξ hξ
    have hDZAc : DZ Ac ξ = starRingEnd ℂ (WirtingerIter 1 1 H ξ) := by
      rw [hAc, (WirtingerConjRule A ξ hdA).1, hDZbarA]
    have hDZBc : DZ Bc ξ = starRingEnd ℂ (WirtingerIter 0 2 H ξ) := by
      rw [hBc, (WirtingerConjRule B ξ hdB).1, hDZbarB]
    -- Step 5: the two products
    obtain ⟨F1, hF1⟩ : ∃ f : ℂ → ℂ, f = fun z => A z * Ac z := ⟨_, rfl⟩
    obtain ⟨F2, hF2⟩ : ∃ f : ℂ → ℂ, f = fun z => B z * Bc z := ⟨_, rfl⟩
    have hdF1 : DifferentiableAt ℝ F1 ξ := by rw [hF1]; exact hdA.mul hdAc
    have hdF2 : DifferentiableAt ℝ F2 ξ := by rw [hF2]; exact hdB.mul hdBc
    have hvF1 : DZ F1 ξ = WirtingerIter 2 0 H ξ * starRingEnd ℂ (WirtingerIter 1 0 H ξ)
        + WirtingerIter 1 0 H ξ * starRingEnd ℂ (WirtingerIter 1 1 H ξ) := by
      rw [hF1, (WirtingerProductRule A Ac ξ hdA hdAc).1, hDZA, hDZAc, hAc, hA]
    have hvF2 : DZ F2 ξ = WirtingerIter 1 1 H ξ * starRingEnd ℂ (WirtingerIter 0 1 H ξ)
        + WirtingerIter 0 1 H ξ * starRingEnd ℂ (WirtingerIter 0 2 H ξ) := by
      rw [hF2, (WirtingerProductRule B Bc ξ hdB hdBc).1, hDZB, hDZBc, hBc, hB]
    -- Step 6: `funext` makes `J` and the product expression the SAME function
    have hsub : ∀ (f g : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ f ζ → DifferentiableAt ℝ g ζ →
        DZ (fun z => f z - g z) ζ = DZ f ζ - DZ g ζ := by
      intro f g ζ hf hg
      have hd : fderiv ℝ (fun z => f z - g z) ζ = fderiv ℝ f ζ - fderiv ℝ g ζ :=
        (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
      rw [DZ, DZ, DZ, hd]
      simp only [sub_apply]
      ring
    have hJfun : (fun ζ => ((Jac H ζ : ℝ) : ℂ)) = fun ζ => F1 ζ - F2 ζ := by
      funext ζ
      rw [hF1, hF2, hAc, hBc, hA, hB]
      exact hJval ζ
    rw [hJfun, hsub F1 F2 ξ hdF1 hdF2, hvF1, hvF2]
    ring
