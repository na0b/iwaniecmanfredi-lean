import IwaniecManfredi.PClass
import IwaniecManfredi.PartialWord

/-- The growth estimate for members of the class `ℙ(s,k)` of Section 5 of the
paper: if every partial derivative of `H` of order `m` is `O(|ξ|^{g-m})`, then
every `P ∈ ℙ(s,k)` is `O(|ξ|^{kg-s})`.  This is the paper's display at
`paper.tex:488`, `|Q| ≤ M|ξ|^{g-s_1}⋯|ξ|^{g-s_k} = M|ξ|^{kg-s}` for a
monomial of type `(s,k)`, summed over the finite linear combination that
`PClass` carries as its witnessing presentation.  Applied with `g = γ_n` and
`P_ν ∈ ℙ(4l-3, 3l-2)` it gives the exponent `(3l-2)γ_n - 4l + 3`. -/
theorem PClassGrowthBound (H : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) (hne : ∀ ξ ∈ Ω, ξ ≠ 0)
    (g : ℝ) (Cm : ℕ → ℝ)
    (h43 : ∀ (m : ℕ), ∀ ξ ∈ Ω,
      ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        ≤ Cm m * ‖ξ‖ ^ (g - (m : ℝ)))
    (s k : ℕ) (P : ℂ → ℂ) (hP : PClass H s k P) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ Ω,
      ‖P ξ‖ ≤ M * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := by
  -- ## Step 0: the empty case, which has no point at which to read off `Cm q ≥ 0`
  rcases Set.eq_empty_or_nonempty Ω with hemp | ⟨ξ0, hξ0⟩
  · refine ⟨0, le_refl 0, ?_⟩
    intro ξ hξ
    rw [hemp] at hξ
    exact absurd hξ (by simp)
  have hnormpos : ∀ ξ ∈ Ω, (0 : ℝ) < ‖ξ‖ := fun ξ hξ => norm_pos_iff.mpr (hne ξ hξ)
  -- ## Step 1: `Cm m ≥ 0`
  have hCm : ∀ m : ℕ, 0 ≤ Cm m := by
    intro m
    have hp : (0 : ℝ) < ‖ξ0‖ ^ (g - (m : ℝ)) := Real.rpow_pos_of_pos (hnormpos ξ0 hξ0) _
    have h0 : (0 : ℝ) ≤ Cm m * ‖ξ0‖ ^ (g - (m : ℝ)) :=
      le_trans (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (h43 m ξ0 hξ0)
    nlinarith [h0, hp]
  -- ## The per-word form of the hypothesis: a single summand is at most the sum
  have hword : ∀ (w : List (Fin 2)), ∀ ξ ∈ Ω,
      ‖PartialWord w H ξ‖ ≤ Cm w.length * ‖ξ‖ ^ (g - (w.length : ℝ)) := by
    intro w ξ hξ
    refine le_trans ?_ (h43 w.length ξ hξ)
    have hofn : List.ofFn (w.get) = w := List.ofFn_get w
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum
      (f := fun v : Fin w.length → Fin 2 => ‖PartialWord (List.ofFn v) H ξ‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ w.get))
    rw [hofn]
  -- ## Differentiability of every word derivative of `H` on `Ω`
  have hPWcd : ∀ (w : List (Fin 2)) (f : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      ContDiffOn ℝ (⊤ : ℕ∞) f U → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) U := by
    intro w
    induction w with
    | nil => intro f U _ hf; exact hf
    | cons j w ih =>
        intro f U hU hf
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) U := ih f U hU hf
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w f)) U :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  have hPWd : ∀ (w : List (Fin 2)) (ξ : ℂ), ξ ∈ Ω → DifferentiableAt ℝ (PartialWord w H) ξ :=
    fun w ξ hξ =>
      ((hPWcd w H Ω hΩ hH).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ)
  -- the head of a word is the OUTERMOST derivative: `rfl`-level
  have hpw0 : ∀ (w : List (Fin 2)) (ζ : ℂ),
      fderiv ℝ (PartialWord w H) ζ 1 = PartialWord ((0 : Fin 2) :: w) H ζ := fun _ _ => rfl
  have hpw1 : ∀ (w : List (Fin 2)) (ζ : ℂ),
      fderiv ℝ (PartialWord w H) ζ Complex.I = PartialWord ((1 : Fin 2) :: w) H ζ :=
    fun _ _ => rfl
  -- ## Differentiating the list identity: `fderiv` of a `List.sum`
  have hlistfd : ∀ (L : List (ℂ × List (Fin 2))) (ξ : ℂ), ξ ∈ Ω →
      DifferentiableAt ℝ (fun ζ => (L.map (fun cw => cw.1 * PartialWord cw.2 H ζ)).sum) ξ ∧
      ∀ v : ℂ, fderiv ℝ (fun ζ => (L.map (fun cw => cw.1 * PartialWord cw.2 H ζ)).sum) ξ v
        = (L.map (fun cw => cw.1 * fderiv ℝ (PartialWord cw.2 H) ξ v)).sum := by
    intro L ξ hξ
    induction L with
    | nil =>
        refine ⟨?_, ?_⟩
        · simp
        · intro v
          simp
    | cons cw T ih =>
        obtain ⟨ihd, ihv⟩ := ih
        have hfe : (fun ζ => ((cw :: T).map (fun c => c.1 * PartialWord c.2 H ζ)).sum)
            = fun ζ => cw.1 * PartialWord cw.2 H ζ
                + (T.map (fun c => c.1 * PartialWord c.2 H ζ)).sum := by
          funext ζ
          simp
        have h1 : HasFDerivAt (fun ζ => cw.1 * PartialWord cw.2 H ζ)
            (cw.1 • fderiv ℝ (PartialWord cw.2 H) ξ) ξ :=
          (hPWd cw.2 ξ hξ).hasFDerivAt.const_mul cw.1
        have h3 : HasFDerivAt (fun ζ => cw.1 * PartialWord cw.2 H ζ
              + (T.map (fun c => c.1 * PartialWord c.2 H ζ)).sum)
            (cw.1 • fderiv ℝ (PartialWord cw.2 H) ξ
              + fderiv ℝ (fun ζ => (T.map (fun c => c.1 * PartialWord c.2 H ζ)).sum) ξ) ξ :=
          h1.add ihd.hasFDerivAt
        rw [hfe]
        refine ⟨h3.differentiableAt, ?_⟩
        intro v
        rw [h3.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [ihv v]
        simp
  -- ## `DZ` and `DZbar` only see a function through its values on the open set `Ω`
  have hcongr : ∀ (f₁ f₂ : ℂ → ℂ) (ξ : ℂ), ξ ∈ Ω → (∀ ζ ∈ Ω, f₁ ζ = f₂ ζ) →
      DZ f₁ ξ = DZ f₂ ξ ∧ DZbar f₁ ξ = DZbar f₂ ξ := by
    intro f₁ f₂ ξ hξ h
    have hev : f₁ =ᶠ[nhds ξ] f₂ := by
      filter_upwards [hΩ.mem_nhds hξ] with ζ hζ using h ζ hζ
    exact ⟨by rw [DZ, DZ, hev.fderiv_eq], by rw [DZbar, DZbar, hev.fderiv_eq]⟩
  -- ## The list step: prepending the two directions, with `‖a‖ + ‖b‖ ≤ 1`
  have hstep : ∀ (a b : ℂ), ‖a‖ + ‖b‖ ≤ 1 → ∀ (n : ℕ) (L : List (ℂ × List (Fin 2))),
      (L.map (fun cw => ‖cw.1‖)).sum ≤ 1 → (∀ cw ∈ L, cw.2.length = n) →
      ∃ L' : List (ℂ × List (Fin 2)),
        (L'.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L', cw.2.length = n + 1) ∧
        ∀ ξ : ℂ, (L'.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum
          = a * (L.map (fun cw => cw.1 * PartialWord ((0 : Fin 2) :: cw.2) H ξ)).sum
            + b * (L.map (fun cw => cw.1 * PartialWord ((1 : Fin 2) :: cw.2) H ξ)).sum := by
    intro a b hab n L hLn hLlen
    refine ⟨L.flatMap (fun cw => [(a * cw.1, (0 : Fin 2) :: cw.2),
      (b * cw.1, (1 : Fin 2) :: cw.2)]), ?_, ?_, ?_⟩
    · have hnsum : ∀ A : List (ℂ × List (Fin 2)),
          ((A.flatMap (fun cw => [(a * cw.1, (0 : Fin 2) :: cw.2),
              (b * cw.1, (1 : Fin 2) :: cw.2)])).map (fun cw => ‖cw.1‖)).sum
            = (‖a‖ + ‖b‖) * (A.map (fun cw => ‖cw.1‖)).sum := by
        intro A
        induction A with
        | nil => simp
        | cons cw T ih =>
            rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_mul]
            ring
      rw [hnsum L]
      have hs0 : (0 : ℝ) ≤ (L.map (fun cw => ‖cw.1‖)).sum := by
        refine List.sum_nonneg ?_
        intro x hx
        obtain ⟨cw, _, rfl⟩ := List.mem_map.mp hx
        exact norm_nonneg _
      nlinarith [hab, hLn, hs0]
    · intro cw hcw
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hcw
      obtain ⟨cw0, hcw0, h | h⟩ := hcw
      · rw [h]
        simp only [List.length_cons]
        rw [hLlen cw0 hcw0]
      · rw [h]
        simp only [List.length_cons]
        rw [hLlen cw0 hcw0]
    · intro ξ
      have hv : ∀ A : List (ℂ × List (Fin 2)),
          ((A.flatMap (fun cw => [(a * cw.1, (0 : Fin 2) :: cw.2),
              (b * cw.1, (1 : Fin 2) :: cw.2)])).map
                (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum
            = a * (A.map (fun cw => cw.1 * PartialWord ((0 : Fin 2) :: cw.2) H ξ)).sum
              + b * (A.map (fun cw => cw.1 * PartialWord ((1 : Fin 2) :: cw.2) H ξ)).sum := by
        intro A
        induction A with
        | nil => simp
        | cons cw T ih =>
            rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
            ring
      exact hv L
  -- ## Step 2: every iterated Wirtinger derivative is a short combination of word derivatives
  have hbase : ∃ L : List (ℂ × List (Fin 2)),
      (L.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L, cw.2.length = 0) ∧
      ∀ ξ ∈ Ω, WirtingerIter 0 0 H ξ
        = (L.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum := by
    refine ⟨[((1 : ℂ), ([] : List (Fin 2)))], by simp, ?_, ?_⟩
    · intro cw hcw
      simp only [List.mem_singleton] at hcw
      simp [hcw]
    · intro ξ _
      simp [WirtingerIter, PartialWord]
  have hDZstep : ∀ (F : ℂ → ℂ) (n : ℕ) (L : List (ℂ × List (Fin 2))),
      (L.map (fun cw => ‖cw.1‖)).sum ≤ 1 → (∀ cw ∈ L, cw.2.length = n) →
      (∀ ξ ∈ Ω, F ξ = (L.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum) →
      (∃ L1 : List (ℂ × List (Fin 2)),
          (L1.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L1, cw.2.length = n + 1) ∧
          ∀ ξ ∈ Ω, DZ F ξ = (L1.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum) ∧
      (∃ L2 : List (ℂ × List (Fin 2)),
          (L2.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L2, cw.2.length = n + 1) ∧
          ∀ ξ ∈ Ω, DZbar F ξ = (L2.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum) := by
    intro F n L hLn hLlen hLval
    have hnab : ‖(1 / 2 : ℂ)‖ + ‖-Complex.I / 2‖ ≤ 1 := by
      norm_num [Complex.norm_I]
    have hnab' : ‖(1 / 2 : ℂ)‖ + ‖Complex.I / 2‖ ≤ 1 := by
      norm_num [Complex.norm_I]
    obtain ⟨L1, h1n, h1len, h1v⟩ := hstep (1 / 2 : ℂ) (-Complex.I / 2) hnab n L hLn hLlen
    obtain ⟨L2, h2n, h2len, h2v⟩ := hstep (1 / 2 : ℂ) (Complex.I / 2) hnab' n L hLn hLlen
    refine ⟨⟨L1, h1n, h1len, ?_⟩, ⟨L2, h2n, h2len, ?_⟩⟩
    · intro ξ hξ
      rw [(hcongr F _ ξ hξ hLval).1, DZ]
      obtain ⟨_, hv⟩ := hlistfd L ξ hξ
      rw [hv 1, hv Complex.I, h1v ξ]
      simp only [hpw0, hpw1]
      ring
    · intro ξ hξ
      rw [(hcongr F _ ξ hξ hLval).2, DZbar]
      obtain ⟨_, hv⟩ := hlistfd L ξ hξ
      rw [hv 1, hv Complex.I, h2v ξ]
      simp only [hpw0, hpw1]
      ring
  have keyJ : ∀ j : ℕ, ∃ L : List (ℂ × List (Fin 2)),
      (L.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L, cw.2.length = 0 + j) ∧
      ∀ ξ ∈ Ω, WirtingerIter 0 j H ξ
        = (L.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
        obtain ⟨L, hLn, hLlen, hLval⟩ := ih
        obtain ⟨-, L2, h2n, h2len, h2v⟩ :=
          hDZstep (WirtingerIter 0 j H) (0 + j) L hLn hLlen hLval
        refine ⟨L2, h2n, by simpa using h2len, ?_⟩
        intro ξ hξ
        have he : WirtingerIter 0 (j + 1) H = DZbar (WirtingerIter 0 j H) := by
          simp only [WirtingerIter, Function.iterate_succ_apply',
            Function.iterate_zero_apply]
        rw [he]
        exact h2v ξ hξ
  have key : ∀ i j : ℕ, ∃ L : List (ℂ × List (Fin 2)),
      (L.map (fun cw => ‖cw.1‖)).sum ≤ 1 ∧ (∀ cw ∈ L, cw.2.length = i + j) ∧
      ∀ ξ ∈ Ω, WirtingerIter i j H ξ
        = (L.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum := by
    intro i j
    induction i with
    | zero => exact keyJ j
    | succ i ih =>
        obtain ⟨L, hLn, hLlen, hLval⟩ := ih
        obtain ⟨⟨L1, h1n, h1len, h1v⟩, -⟩ :=
          hDZstep (WirtingerIter i j H) (i + j) L hLn hLlen hLval
        refine ⟨L1, h1n, by intro cw hcw; rw [h1len cw hcw]; omega, ?_⟩
        intro ξ hξ
        have he : WirtingerIter (i + 1) j H = DZ (WirtingerIter i j H) := by
          rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
        rw [he]
        exact h1v ξ hξ
  -- ## The bound on a symbol value
  have hlistbound : ∀ (L : List (ℂ × List (Fin 2))) (ξ : ℂ) (B : ℝ), 0 ≤ B →
      (∀ cw ∈ L, ‖PartialWord cw.2 H ξ‖ ≤ B) →
      ‖(L.map (fun cw => cw.1 * PartialWord cw.2 H ξ)).sum‖
        ≤ (L.map (fun cw => ‖cw.1‖)).sum * B := by
    intro L ξ B hB
    induction L with
    | nil => intro _; simp
    | cons cw T ih =>
        intro hall
        have h1 : ‖cw.1 * PartialWord cw.2 H ξ‖ ≤ ‖cw.1‖ * B := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hall cw (List.mem_cons_self ..)) (norm_nonneg _)
        have h2 := ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))
        simp only [List.map_cons, List.sum_cons]
        refine le_trans (norm_add_le _ _) ?_
        calc ‖cw.1 * PartialWord cw.2 H ξ‖
              + ‖(T.map (fun c => c.1 * PartialWord c.2 H ξ)).sum‖
            ≤ ‖cw.1‖ * B + (T.map (fun c => ‖c.1‖)).sum * B := add_le_add h1 h2
          _ = (‖cw.1‖ + (T.map (fun c => ‖c.1‖)).sum) * B := by ring
  have hsym : ∀ (d : DerivSymbol), ∀ ξ ∈ Ω,
      ‖SymbolValue H d ξ‖ ≤ Cm (d.i + d.j) * ‖ξ‖ ^ (g - ((d.i + d.j : ℕ) : ℝ)) := by
    intro d ξ hξ
    obtain ⟨L, hLn, hLlen, hLval⟩ := key d.i d.j
    have hB : (0 : ℝ) ≤ Cm (d.i + d.j) * ‖ξ‖ ^ (g - ((d.i + d.j : ℕ) : ℝ)) :=
      mul_nonneg (hCm _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hall : ∀ cw ∈ L, ‖PartialWord cw.2 H ξ‖
        ≤ Cm (d.i + d.j) * ‖ξ‖ ^ (g - ((d.i + d.j : ℕ) : ℝ)) := by
      intro cw hcw
      have := hword cw.2 ξ hξ
      rw [hLlen cw hcw] at this
      exact this
    have hWb : ‖WirtingerIter d.i d.j H ξ‖
        ≤ Cm (d.i + d.j) * ‖ξ‖ ^ (g - ((d.i + d.j : ℕ) : ℝ)) := by
      rw [hLval ξ hξ]
      refine le_trans (hlistbound L ξ _ hB hall) ?_
      nlinarith [hLn, hB, mul_nonneg (sub_nonneg.mpr hLn) hB]
    unfold SymbolValue
    by_cases hc : d.conjugated
    · simp only [hc, if_pos]
      rw [RCLike.norm_conj]
      exact hWb
    · simp only [hc, Bool.false_eq_true]
      exact hWb
  -- ## Step 3: the monomial bound, generalized over the list of symbols
  have hmon : ∀ (N : List DerivSymbol), ∀ ξ ∈ Ω,
      ‖MonomialValue H N ξ‖ ≤ (N.map (fun d => Cm (d.i + d.j))).prod
        * ‖ξ‖ ^ ((N.length : ℝ) * g
            - (((N.map (fun d => d.i + d.j)).sum : ℕ) : ℝ)) := by
    intro N
    induction N with
    | nil =>
        intro ξ _
        simp [MonomialValue]
    | cons d T ih =>
        intro ξ hξ
        have hxp : (0 : ℝ) < ‖ξ‖ := hnormpos ξ hξ
        have hprodT : (0 : ℝ) ≤ (T.map (fun d => Cm (d.i + d.j))).prod := by
          refine List.prod_nonneg ?_
          intro x hx
          obtain ⟨d0, _, rfl⟩ := List.mem_map.mp hx
          exact hCm _
        have hfe : MonomialValue H (d :: T) ξ = SymbolValue H d ξ * MonomialValue H T ξ := by
          simp [MonomialValue]
        have h1 := hsym d ξ hξ
        have h2 := ih ξ hξ
        rw [hfe, norm_mul]
        have hmul : ‖SymbolValue H d ξ‖ * ‖MonomialValue H T ξ‖
            ≤ (Cm (d.i + d.j) * ‖ξ‖ ^ (g - ((d.i + d.j : ℕ) : ℝ)))
              * ((T.map (fun d => Cm (d.i + d.j))).prod
                  * ‖ξ‖ ^ ((T.length : ℝ) * g
                      - (((T.map (fun d => d.i + d.j)).sum : ℕ) : ℝ))) := by
          refine mul_le_mul h1 h2 (norm_nonneg _) ?_
          exact mul_nonneg (hCm _) (Real.rpow_nonneg (norm_nonneg _) _)
        refine le_trans hmul (le_of_eq ?_)
        simp only [List.length_cons, List.map_cons, List.prod_cons, List.sum_cons]
        rw [mul_mul_mul_comm]
        congr 1
        rw [← Real.rpow_add hxp]
        congr 1
        push_cast
        ring
  -- ## Step 4: the linear combination
  obtain ⟨L, hdeg, hval⟩ := hP
  obtain ⟨Mconst, hMdef⟩ : ∃ x : ℝ, x =
      (L.map (fun cm => ‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)).sum := ⟨_, rfl⟩
  have hMnn : 0 ≤ Mconst := by
    rw [hMdef]
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨cm, _, rfl⟩ := List.mem_map.mp hx
    refine mul_nonneg (norm_nonneg _) (List.prod_nonneg ?_)
    intro y hy
    obtain ⟨d0, _, rfl⟩ := List.mem_map.mp hy
    exact hCm _
  refine ⟨Mconst, hMnn, ?_⟩
  intro ξ hξ
  have hsumbound : ∀ A : List (ℂ × List DerivSymbol),
      (∀ cm ∈ A, (cm.2.map (fun d => d.i + d.j)).sum = s ∧ cm.2.length = k) →
      ‖(A.map (fun cm => cm.1 * MonomialValue H cm.2 ξ)).sum‖
        ≤ (A.map (fun cm => ‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)).sum
            * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := by
    intro A
    induction A with
    | nil =>
        intro _
        simp
    | cons cm T ih =>
        intro hall
        obtain ⟨hs1, hs2⟩ := hall cm (List.mem_cons_self ..)
        have h1 : ‖cm.1 * MonomialValue H cm.2 ξ‖
            ≤ (‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)
                * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := by
          have hm := hmon cm.2 ξ hξ
          rw [hs1, hs2] at hm
          rw [norm_mul]
          calc ‖cm.1‖ * ‖MonomialValue H cm.2 ξ‖
              ≤ ‖cm.1‖ * ((cm.2.map (fun d => Cm (d.i + d.j))).prod
                  * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ))) :=
                mul_le_mul_of_nonneg_left hm (norm_nonneg _)
            _ = (‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)
                  * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := by ring
        have h2 := ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))
        simp only [List.map_cons, List.sum_cons]
        refine le_trans (norm_add_le _ _) ?_
        calc ‖cm.1 * MonomialValue H cm.2 ξ‖
              + ‖(T.map (fun c => c.1 * MonomialValue H c.2 ξ)).sum‖
            ≤ (‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)
                * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ))
              + (T.map (fun c => ‖c.1‖ * (c.2.map (fun d => Cm (d.i + d.j))).prod)).sum
                * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := add_le_add h1 h2
          _ = ((‖cm.1‖ * (cm.2.map (fun d => Cm (d.i + d.j))).prod)
                + (T.map (fun c => ‖c.1‖ * (c.2.map (fun d => Cm (d.i + d.j))).prod)).sum)
                * ‖ξ‖ ^ ((k : ℝ) * g - (s : ℝ)) := by ring
  rw [hval ξ, hMdef]
  exact hsumbound L hdeg
