import IwaniecManfredi.PClass

/-- Property (iii) of Section 5 of the paper: if `P ∈ ℙ(s,k)` and
`Q ∈ ℙ(t,l)` then `PQ ∈ ℙ(s+t, k+l)`. -/
theorem PClassMulClosed (H : ℂ → ℂ) (s k t l : ℕ) (P Q : ℂ → ℂ)
    (hP : PClass H s k P) (hQ : PClass H t l Q) :
    PClass H (s + t) (k + l) (fun ξ => P ξ * Q ξ) := by
  obtain ⟨LP, hPdeg, hPval⟩ := hP
  obtain ⟨LQ, hQdeg, hQval⟩ := hQ
  have hmonapp : ∀ (M1 M2 : List DerivSymbol) (ξ : ℂ),
      MonomialValue H (M1 ++ M2) ξ = MonomialValue H M1 ξ * MonomialValue H M2 ξ := by
    intro M1 M2 ξ
    unfold MonomialValue
    rw [List.map_append, List.prod_append]
  refine ⟨LP.flatMap (fun cp => LQ.map (fun cq => (cp.1 * cq.1, cp.2 ++ cq.2))), ?_, ?_⟩
  · intro cm hcm
    simp only [List.mem_flatMap, List.mem_map] at hcm
    obtain ⟨cp, hcp, cq, hcq, rfl⟩ := hcm
    obtain ⟨hp1, hp2⟩ := hPdeg cp hcp
    obtain ⟨hq1, hq2⟩ := hQdeg cq hcq
    refine ⟨?_, ?_⟩
    · simp only [List.map_append, List.sum_append, hp1, hq1]
    · simp only [List.length_append, hp2, hq2]
  · intro ξ
    show P ξ * Q ξ = _
    have hdist : ∀ A : List (ℂ × List DerivSymbol),
        ((A.flatMap (fun cp => LQ.map (fun cq => (cp.1 * cq.1, cp.2 ++ cq.2)))).map
            (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum
          = (A.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum
            * (LQ.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum := by
      intro A
      induction A with
      | nil => simp
      | cons cp tp ih =>
          rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
            List.map_cons, List.sum_cons, add_mul]
          congr 1
          rw [List.map_map]
          have : (fun cq : ℂ × List DerivSymbol =>
                (cp.1 * MonomialValue H cp.2 ξ) * (cq.1 * MonomialValue H cq.2 ξ))
              = ((fun cm : ℂ × List DerivSymbol => cm.1 * MonomialValue H cm.2 ξ)
                  ∘ (fun cq : ℂ × List DerivSymbol => (cp.1 * cq.1, cp.2 ++ cq.2))) := by
            funext cq
            simp only [Function.comp_apply, hmonapp]
            ring
          rw [← this, List.sum_map_mul_left]
    rw [hPval ξ, hQval ξ, hdist LP]
