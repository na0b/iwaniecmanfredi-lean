import IwaniecManfredi.PClass
import IwaniecManfredi.WirtingerProductRule
import IwaniecManfredi.WirtingerConjRule
import IwaniecManfredi.WirtingerIterSwap

/-- Property (i) of Section 5 of the paper: if `P ∈ ℙ(s,k)` then
`P_ξ, P_ξ̄ ∈ ℙ(s+1,k)`.  Stated, and to be proved, as a Leibniz computation on
monomials: differentiating a monomial of length `k` produces a sum of `k`
monomials, each with one factor's order raised by one.  The length `k` is
therefore unchanged and the total order rises by exactly one, which is what
keeps the per-factor order structure available to the growth estimate of
Corollary 2. -/
theorem PClassDerivClosed (H : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) (s k : ℕ) (P : ℂ → ℂ) (hP : PClass H s k P) :
    (∃ Q, PClass H (s + 1) k Q ∧ ∀ ξ ∈ Ω, DZ P ξ = Q ξ) ∧
      (∃ Q, PClass H (s + 1) k Q ∧ ∀ ξ ∈ Ω, DZbar P ξ = Q ξ) := by
  obtain ⟨L, hLdeg, hLval⟩ := hP
  -- ## Step 1: every symbol value is `C^∞` on `Ω`
  have hconjcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) :=
    Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hsym : ∀ d : DerivSymbol, ContDiffOn ℝ (⊤ : ℕ∞) (SymbolValue H d) Ω := by
    intro d
    have hg := (WirtingerIterSwap H Ω hΩ hH d.i d.j).1
    unfold SymbolValue
    by_cases hc : d.conjugated
    · simp only [hc, if_true]
      exact hconjcd.comp_contDiffOn hg
    · simp only [hc]
      exact hg
  have hsymd : ∀ (d : DerivSymbol) (ξ : ℂ), ξ ∈ Ω →
      DifferentiableAt ℝ (SymbolValue H d) ξ := by
    intro d ξ hξ
    exact ((hsym d).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ)
  have hmondiff : ∀ (M : List DerivSymbol) (ξ : ℂ), ξ ∈ Ω →
      DifferentiableAt ℝ (MonomialValue H M) ξ := by
    intro M
    induction M with
    | nil =>
        intro ξ _
        have h1 : MonomialValue H ([] : List DerivSymbol) = fun _ : ℂ => (1 : ℂ) := by
          funext z; simp [MonomialValue]
        rw [h1]
        exact differentiableAt_const 1
    | cons d M' ih =>
        intro ξ hξ
        have hfe : MonomialValue H (d :: M')
            = fun z => SymbolValue H d z * MonomialValue H M' z := by
          funext z; simp [MonomialValue]
        rw [hfe]
        exact (hsymd d ξ hξ).mul (ih ξ hξ)
  have hsumdiff : ∀ (L0 : List (ℂ × List DerivSymbol)) (ξ : ℂ), ξ ∈ Ω →
      DifferentiableAt ℝ
        (fun ζ => (L0.map (fun cm => cm.1 * MonomialValue H cm.2 ζ)).sum) ξ := by
    intro L0
    induction L0 with
    | nil =>
        intro ξ _
        simp
    | cons cm T ih =>
        intro ξ hξ
        have hfe : (fun ζ => ((cm :: T).map (fun c => c.1 * MonomialValue H c.2 ζ)).sum)
            = fun ζ => cm.1 * MonomialValue H cm.2 ζ
                + (T.map (fun c => c.1 * MonomialValue H c.2 ζ)).sum := by
          funext ζ; simp
        rw [hfe]
        exact ((differentiableAt_const cm.1).mul (hmondiff cm.2 ξ hξ)).add (ih ξ hξ)
  -- ## Step 2: differentiating one symbol value raises its order by one
  obtain ⟨Dp, hDpord, hDpval⟩ : ∃ F : DerivSymbol → DerivSymbol,
      (∀ d : DerivSymbol, (F d).i + (F d).j = d.i + d.j + 1) ∧
      (∀ (d : DerivSymbol) (ξ : ℂ), ξ ∈ Ω →
        DZ (SymbolValue H d) ξ = SymbolValue H (F d) ξ) := by
    refine ⟨fun d => if d.conjugated then ⟨d.i, d.j + 1, true, by omega⟩
      else ⟨d.i + 1, d.j, false, by omega⟩, ?_, ?_⟩
    · intro d
      by_cases hc : d.conjugated <;> simp [hc] <;> omega
    · intro d ξ hξ
      by_cases hc : d.conjugated
      · have hg : DifferentiableAt ℝ (WirtingerIter d.i d.j H) ξ :=
          (((WirtingerIterSwap H Ω hΩ hH d.i d.j).1).differentiableOn
            (by simp)).differentiableAt (hΩ.mem_nhds hξ)
        have h1 := (WirtingerConjRule (WirtingerIter d.i d.j H) ξ hg).1
        have h2 := (WirtingerIterSwap H Ω hΩ hH d.i d.j).2 ξ hξ
        simp only [SymbolValue, hc, if_pos]
        rw [h1, h2]
      · have he : WirtingerIter (d.i + 1) d.j H = DZ (WirtingerIter d.i d.j H) := by
          rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
        simp only [SymbolValue, hc, if_false, Bool.false_eq_true]
        rw [he]
  obtain ⟨Dm, hDmord, hDmval⟩ : ∃ F : DerivSymbol → DerivSymbol,
      (∀ d : DerivSymbol, (F d).i + (F d).j = d.i + d.j + 1) ∧
      (∀ (d : DerivSymbol) (ξ : ℂ), ξ ∈ Ω →
        DZbar (SymbolValue H d) ξ = SymbolValue H (F d) ξ) := by
    refine ⟨fun d => if d.conjugated then ⟨d.i + 1, d.j, true, by omega⟩
      else ⟨d.i, d.j + 1, false, by omega⟩, ?_, ?_⟩
    · intro d
      by_cases hc : d.conjugated <;> simp [hc] <;> omega
    · intro d ξ hξ
      by_cases hc : d.conjugated
      · have hg : DifferentiableAt ℝ (WirtingerIter d.i d.j H) ξ :=
          (((WirtingerIterSwap H Ω hΩ hH d.i d.j).1).differentiableOn
            (by simp)).differentiableAt (hΩ.mem_nhds hξ)
        have h1 := (WirtingerConjRule (WirtingerIter d.i d.j H) ξ hg).2
        have he : WirtingerIter (d.i + 1) d.j H = DZ (WirtingerIter d.i d.j H) := by
          rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
        simp only [SymbolValue, hc, if_pos]
        rw [h1, he]
      · have h2 := (WirtingerIterSwap H Ω hΩ hH d.i d.j).2 ξ hξ
        simp only [SymbolValue, hc, if_false, Bool.false_eq_true]
        rw [h2]
  -- ## Steps 3 and 4, uniformly in the operator
  have hgen : ∀ (D : (ℂ → ℂ) → ℂ → ℂ) (F : DerivSymbol → DerivSymbol),
      (∀ (f g : ℂ → ℂ) (ξ : ℂ), DifferentiableAt ℝ f ξ → DifferentiableAt ℝ g ξ →
        D (fun z => f z * g z) ξ = D f ξ * g ξ + f ξ * D g ξ) →
      (∀ (f g : ℂ → ℂ) (ξ : ℂ), DifferentiableAt ℝ f ξ → DifferentiableAt ℝ g ξ →
        D (fun z => f z + g z) ξ = D f ξ + D g ξ) →
      (∀ (c : ℂ) (ξ : ℂ), D (fun _ => c) ξ = 0) →
      (∀ (c : ℂ) (f : ℂ → ℂ) (ξ : ℂ), DifferentiableAt ℝ f ξ →
        D (fun z => c * f z) ξ = c * D f ξ) →
      (∀ d : DerivSymbol, (F d).i + (F d).j = d.i + d.j + 1) →
      (∀ (d : DerivSymbol) (ξ : ℂ), ξ ∈ Ω →
        D (SymbolValue H d) ξ = SymbolValue H (F d) ξ) →
      ∃ Q, PClass H (s + 1) k Q ∧ ∀ ξ ∈ Ω, D P ξ = Q ξ := by
    intro D F hprod hadd hconst hsmul hFord hFval
    -- ### Step 3: Leibniz on a monomial
    have hleib : ∀ M : List DerivSymbol, ∃ R : List (List DerivSymbol),
        (∀ N ∈ R, N.length = M.length ∧
          (N.map (fun d => d.i + d.j)).sum = (M.map (fun d => d.i + d.j)).sum + 1) ∧
        ∀ ξ ∈ Ω, D (MonomialValue H M) ξ
          = (R.map (fun N => MonomialValue H N ξ)).sum := by
      intro M
      induction M with
      | nil =>
          refine ⟨[], by simp, ?_⟩
          intro ξ _
          have h1 : MonomialValue H ([] : List DerivSymbol) = fun _ : ℂ => (1 : ℂ) := by
            funext z; simp [MonomialValue]
          rw [h1, hconst]
          simp
      | cons d M' ih =>
          obtain ⟨R', hR'deg, hR'val⟩ := ih
          refine ⟨(F d :: M') :: R'.map (fun N => d :: N), ?_, ?_⟩
          · intro N hN
            rcases List.mem_cons.mp hN with h | h
            · subst h
              refine ⟨by simp, ?_⟩
              simp only [List.map_cons, List.sum_cons, hFord d]
              omega
            · obtain ⟨N0, hN0, rfl⟩ := List.mem_map.mp h
              obtain ⟨h1, h2⟩ := hR'deg N0 hN0
              refine ⟨by simp [h1], ?_⟩
              simp only [List.map_cons, List.sum_cons, h2]
              omega
          · intro ξ hξ
            have hfe : MonomialValue H (d :: M')
                = fun z => SymbolValue H d z * MonomialValue H M' z := by
              funext z; simp [MonomialValue]
            have hmc : ∀ (e : DerivSymbol) (N : List DerivSymbol),
                MonomialValue H (e :: N) ξ = SymbolValue H e ξ * MonomialValue H N ξ := by
              intro e N; simp [MonomialValue]
            rw [hfe, hprod _ _ ξ (hsymd d ξ hξ) (hmondiff M' ξ hξ), hFval d ξ hξ,
              hR'val ξ hξ, List.map_cons, List.sum_cons, hmc, List.map_map]
            have hh : ((fun N => MonomialValue H N ξ) ∘ (fun N => d :: N))
                = fun N => SymbolValue H d ξ * MonomialValue H N ξ := by
              funext N
              simp only [Function.comp_apply]
              rw [hmc]
            rw [hh, List.sum_map_mul_left]
    -- ### Step 4: assembling the witness
    have hsum : ∀ L0 : List (ℂ × List DerivSymbol),
        (∀ cm ∈ L0, (cm.2.map (fun d => d.i + d.j)).sum = s ∧ cm.2.length = k) →
        ∃ L' : List (ℂ × List DerivSymbol),
          (∀ cm ∈ L', (cm.2.map (fun d => d.i + d.j)).sum = s + 1 ∧ cm.2.length = k) ∧
          ∀ ξ ∈ Ω, D (fun ζ => (L0.map (fun cm => cm.1 * MonomialValue H cm.2 ζ)).sum) ξ
            = (L'.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum := by
      intro L0
      induction L0 with
      | nil =>
          intro _
          refine ⟨[], by simp, ?_⟩
          intro ξ _
          have h1 : (fun ζ : ℂ =>
              (([] : List (ℂ × List DerivSymbol)).map
                (fun cm => cm.1 * MonomialValue H cm.2 ζ)).sum) = fun _ : ℂ => (0 : ℂ) := by
            funext z; simp
          rw [h1, hconst]
          simp
      | cons cm T ih =>
          intro hdeg
          obtain ⟨LT, hLTdeg, hLTval⟩ := ih fun x hx => hdeg x (List.mem_cons_of_mem _ hx)
          obtain ⟨R, hRdeg, hRval⟩ := hleib cm.2
          obtain ⟨hcs, hck⟩ := hdeg cm (List.mem_cons_self ..)
          refine ⟨(R.map (fun N => (cm.1, N))) ++ LT, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with h | h
            · obtain ⟨N, hN, rfl⟩ := List.mem_map.mp h
              obtain ⟨h1, h2⟩ := hRdeg N hN
              exact ⟨by rw [h2, hcs], by rw [h1, hck]⟩
            · exact hLTdeg x h
          · intro ξ hξ
            obtain ⟨f1, hf1⟩ : ∃ f : ℂ → ℂ,
                f = fun ζ => cm.1 * MonomialValue H cm.2 ζ := ⟨_, rfl⟩
            obtain ⟨f2, hf2⟩ : ∃ f : ℂ → ℂ,
                f = fun ζ => (T.map (fun c => c.1 * MonomialValue H c.2 ζ)).sum := ⟨_, rfl⟩
            have hd1 : DifferentiableAt ℝ f1 ξ := by
              rw [hf1]
              exact (differentiableAt_const cm.1).mul (hmondiff cm.2 ξ hξ)
            have hd2 : DifferentiableAt ℝ f2 ξ := by
              rw [hf2]
              exact hsumdiff T ξ hξ
            have hv1 : D f1 ξ = cm.1 * D (MonomialValue H cm.2) ξ := by
              rw [hf1]
              exact hsmul cm.1 (MonomialValue H cm.2) ξ (hmondiff cm.2 ξ hξ)
            have hv2 : D f2 ξ = (LT.map (fun c => c.1 * MonomialValue H c.2 ξ)).sum := by
              rw [hf2]
              exact hLTval ξ hξ
            have hfe : (fun ζ => ((cm :: T).map (fun c => c.1 * MonomialValue H c.2 ζ)).sum)
                = fun ζ => f1 ζ + f2 ζ := by
              funext ζ
              rw [hf1, hf2]
              simp
            rw [hfe, hadd f1 f2 ξ hd1 hd2, hv1, hv2, hRval ξ hξ,
              List.map_append, List.sum_append, List.map_map]
            have hh : ((fun c : ℂ × List DerivSymbol => c.1 * MonomialValue H c.2 ξ)
                  ∘ (fun N => (cm.1, N)))
                = fun N => cm.1 * MonomialValue H N ξ := by
              funext N; rfl
            rw [hh, List.sum_map_mul_left]
    obtain ⟨L', hL'deg, hL'val⟩ := hsum L hLdeg
    refine ⟨fun ξ => (L'.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum,
      ⟨L', hL'deg, fun ξ => rfl⟩, ?_⟩
    intro ξ hξ
    have hPe : P = fun ζ => (L.map (fun cm => cm.1 * MonomialValue H cm.2 ζ)).sum :=
      funext hLval
    rw [hPe]
    exact hL'val ξ hξ
  refine ⟨hgen DZ Dp ?_ ?_ ?_ ?_ hDpord hDpval,
    hgen DZbar Dm ?_ ?_ ?_ ?_ hDmord hDmval⟩
  · exact fun f g ξ hf hg => (WirtingerProductRule f g ξ hf hg).1
  · intro f g ξ hf hg
    have hd : fderiv ℝ (fun z => f z + g z) ξ = fderiv ℝ f ξ + fderiv ℝ g ξ :=
      (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
    rw [DZ, DZ, DZ, hd]
    simp only [add_apply]
    ring
  · intro c ξ
    simp [DZ]
  · intro c f ξ hf
    have hd : fderiv ℝ (fun z => c * f z) ξ = c • fderiv ℝ f ξ :=
      (hf.hasFDerivAt.const_mul c).fderiv
    rw [DZ, DZ, hd]
    simp only [smul_apply, smul_eq_mul]
    ring
  · exact fun f g ξ hf hg => (WirtingerProductRule f g ξ hf hg).2
  · intro f g ξ hf hg
    have hd : fderiv ℝ (fun z => f z + g z) ξ = fderiv ℝ f ξ + fderiv ℝ g ξ :=
      (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
    rw [DZbar, DZbar, DZbar, hd]
    simp only [add_apply]
    ring
  · intro c ξ
    simp [DZbar]
  · intro c f ξ hf
    have hd : fderiv ℝ (fun z => c * f z) ξ = c • fderiv ℝ f ξ :=
      (hf.hasFDerivAt.const_mul c).fderiv
    rw [DZbar, DZbar, hd]
    simp only [smul_apply, smul_eq_mul]
    ring
