import IwaniecManfredi.PClass

/-- `ℙ(s,k)` is closed under pointwise complex conjugation: conjugating a
monomial only flips each symbol's conjugation flag, leaving `i`, `j` (hence
the order `i + j`) and the list length untouched.  This is what supplies
`J_ξ̄ ∈ ℙ(3,2)` from `J_ξ ∈ ℙ(3,2)`, since `J` is real-valued. -/
theorem PClassConjClosed (H : ℂ → ℂ) (s k : ℕ) (P : ℂ → ℂ) (hP : PClass H s k P) :
    PClass H s k (fun ξ => starRingEnd ℂ (P ξ)) := by
  set fl : DerivSymbol → DerivSymbol :=
    fun d => { i := d.i, j := d.j, conjugated := !d.conjugated,
               order_pos := d.order_pos } with hfl
  have hsym : ∀ (d : DerivSymbol) (ξ : ℂ),
      starRingEnd ℂ (SymbolValue H d ξ) = SymbolValue H (fl d) ξ := by
    intro d ξ
    unfold SymbolValue
    cases hd : d.conjugated <;> simp [hfl, hd]
  have hmon : ∀ (M : List DerivSymbol) (ξ : ℂ),
      starRingEnd ℂ (MonomialValue H M ξ) = MonomialValue H (M.map fl) ξ := by
    intro M ξ
    unfold MonomialValue
    induction M with
    | nil => simp
    | cons d t ih => simp [map_mul, ih, hsym]
  obtain ⟨L, hdeg, hval⟩ := hP
  refine ⟨L.map (fun cm => (starRingEnd ℂ cm.1, cm.2.map fl)), ?_, ?_⟩
  · intro cm hcm
    simp only [List.mem_map] at hcm
    obtain ⟨cm0, hcm0, rfl⟩ := hcm
    obtain ⟨h1, h2⟩ := hdeg cm0 hcm0
    refine ⟨?_, ?_⟩
    · simpa [List.map_map, Function.comp_def, hfl] using h1
    · simpa using h2
  · intro ξ
    show starRingEnd ℂ (P ξ) = _
    rw [hval ξ, map_list_sum, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro cm _
    simp [map_mul, hmon]
