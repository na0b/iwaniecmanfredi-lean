import IwaniecManfredi.Cor2
import IwaniecManfredi.GammaRatioMinAtOne
import IwaniecManfredi.DExpEqGammaOneInv

/-- The estimates (51) and (52) of Section 6: Corollary 2's bound with the
exponent `n/γ_n` replaced by the `n`-free `d = d(p)`, at an arbitrary singular
point rather than at the origin, and transferred from the complex gradient `f`
to `u` itself.  Three things happen here that the paper states in one line
each (`paper.tex:515-527`): the reduction "we may assume the singular point is
the origin", which is a translation; the minimisation of `n/γ_n` over `n`,
which is where `GammaRatioMinAtOne` and `DExpEqGammaOneInv` enter; and the
passage from (51) to (52) through `u_x = f + conj f`, `u_y = i(f - conj f)`.
The radius must be shrunk to `δ ≤ 1`: the inequality `‖z‖^a ≤ ‖z‖^b` for
`a ≥ b` reverses above `1`. -/
theorem Thm1DerivBounds (n : ℕ) (p : ℝ) (K' : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (hK' : 1 ≤ K')
    (qcp : QCPackage)
    (z₀ : ℂ) (W : Set ℂ) (hW : IsOpen W) (hz₀ : z₀ ∈ W)
    (u : ℂ → ℝ) (f chi H : ℂ → ℂ)
    (h12 : SolvesEq12 p W f) (hf0 : f z₀ = 0)
    (hqchi : QuasiconformalOn K' W chi) (hchi0 : chi z₀ = 0)
    (hfact : ∀ z ∈ W, f z = chi z ^ n)
    (hchism : ContDiffOn ℝ (⊤ : ℕ∞) chi (W \ {z₀}))
    (hsurj : ∀ z ∈ W, H (chi z) = z)
    (hHcont : ContinuousOn H (chi '' W))

    (hg0 : ∀ z ∈ W, PartialWord [0] (fun ζ => ((u ζ : ℝ) : ℂ)) z
      = f z + starRingEnd ℂ (f z))
    (hg1 : ∀ z ∈ W, PartialWord [1] (fun ζ => ((u ζ : ℝ) : ℂ)) z
      = Complex.I * (f z - starRingEnd ℂ (f z))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ B : ℕ → ℝ,
      (∀ (m : ℕ) (z : ℂ), 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
        ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) f z‖
          ≤ B m * ‖z - z₀‖ ^ (DExp p - (m : ℝ))) ∧
      (∀ (m : ℕ) (z : ℂ), 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
        ∑ v : Fin (m + 1) → Fin 2,
            ‖PartialWord (List.ofFn v) (fun ζ => ((u ζ : ℝ) : ℂ)) z‖
          ≤ B m * ‖z - z₀‖ ^ (DExp p - (m : ℝ))) := by
  -- ## Step 0: `d > 0` and `d = 1/γ₁`
  obtain ⟨hγ1, hγd⟩ := DExpEqGammaOneInv p hp
  have hγ1ne : GammaExp 1 p ≠ 0 := ne_of_gt hγ1
  have hd : DExp p = 1 / GammaExp 1 p := by
    field_simp
    linear_combination hγd
  -- ## Shared tool: word derivatives of a `C^∞` function are `C^∞`
  have hPWcd : ∀ (w : List (Fin 2)) (G : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) G S → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w G) S := by
    intro w
    induction w with
    | nil => intro G S _ hG; exact hG
    | cons j w ih =>
        intro G S hS hG
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w G) S := ih G S hS hG
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w G)) S :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hS).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  -- ## Shared tool: word derivatives see a function only through an open set
  have hPWcongr : ∀ (w : List (Fin 2)) (G1 G2 : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      (∀ z ∈ S, G1 z = G2 z) → ∀ z ∈ S, PartialWord w G1 z = PartialWord w G2 z := by
    intro w
    induction w with
    | nil => intro G1 G2 S _ h z hz; exact h z hz
    | cons j w ih =>
        intro G1 G2 S hS h z hz
        have hev : PartialWord w G1 =ᶠ[nhds z] PartialWord w G2 := by
          filter_upwards [hS.mem_nhds hz] with ζ hζ using ih G1 G2 S hS h ζ hζ
        show fderiv ℝ (PartialWord w G1) z _ = fderiv ℝ (PartialWord w G2) z _
        rw [hev.fderiv_eq]
  -- ## Step 1: translation, as an equality of FUNCTIONS
  have htrans : ∀ (w : List (Fin 2)) (F : ℂ → ℂ),
      PartialWord w (fun ζ => F (ζ + z₀)) = fun ζ => PartialWord w F (ζ + z₀) := by
    intro w
    induction w with
    | nil => intro F; rfl
    | cons j w ih =>
        intro F
        funext ζ
        show fderiv ℝ (PartialWord w (fun ζ' => F (ζ' + z₀))) ζ
              (if j = 0 then (1 : ℂ) else Complex.I)
            = fderiv ℝ (PartialWord w F) (ζ + z₀) (if j = 0 then (1 : ℂ) else Complex.I)
        rw [ih F, fderiv_comp_add_right]
  -- ## Shared tool: conjugation commutes with every word derivative, unconditionally
  have hPWconj : ∀ (w : List (Fin 2)) (G : ℂ → ℂ),
      PartialWord w (fun ζ => starRingEnd ℂ (G ζ))
        = fun ζ => starRingEnd ℂ (PartialWord w G ζ) := by
    intro w
    induction w with
    | nil => intro G; rfl
    | cons j w ih =>
        intro G
        funext ζ
        show fderiv ℝ (PartialWord w (fun ζ' => starRingEnd ℂ (G ζ'))) ζ
              (if j = 0 then (1 : ℂ) else Complex.I)
            = starRingEnd ℂ (fderiv ℝ (PartialWord w G) ζ
                (if j = 0 then (1 : ℂ) else Complex.I))
        rw [ih G]
        have hfun : (fun ζ' => starRingEnd ℂ (PartialWord w G ζ'))
            = (fun ζ' => star (PartialWord w G ζ')) := rfl
        rw [hfun, fderiv_star]
        rfl
  -- ## Shared tool: `D^w` is `ℂ`-linear on an open set where both arguments are `C^∞`
  have hPWlin : ∀ (w : List (Fin 2)) (c1 c2 : ℂ) (G1 G2 : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) G1 S → ContDiffOn ℝ (⊤ : ℕ∞) G2 S →
      ∀ z ∈ S, PartialWord w (fun ζ => c1 * G1 ζ + c2 * G2 ζ) z
        = c1 * PartialWord w G1 z + c2 * PartialWord w G2 z := by
    intro w
    induction w with
    | nil => intro c1 c2 G1 G2 S _ _ _ z _; rfl
    | cons j w ih =>
        intro c1 c2 G1 G2 S hS h1 h2 z hz
        have hd1 : DifferentiableAt ℝ (PartialWord w G1) z :=
          ((hPWcd w G1 S hS h1).differentiableOn (by simp)).differentiableAt (hS.mem_nhds hz)
        have hd2 : DifferentiableAt ℝ (PartialWord w G2) z :=
          ((hPWcd w G2 S hS h2).differentiableOn (by simp)).differentiableAt (hS.mem_nhds hz)
        have hev : PartialWord w (fun ζ => c1 * G1 ζ + c2 * G2 ζ)
            =ᶠ[nhds z] fun ζ => c1 * PartialWord w G1 ζ + c2 * PartialWord w G2 ζ := by
          filter_upwards [hS.mem_nhds hz] with ζ hζ using ih c1 c2 G1 G2 S hS h1 h2 ζ hζ
        have hfd : HasFDerivAt (fun ζ => c1 * PartialWord w G1 ζ + c2 * PartialWord w G2 ζ)
            (c1 • fderiv ℝ (PartialWord w G1) z + c2 • fderiv ℝ (PartialWord w G2) z) z :=
          (hd1.hasFDerivAt.const_mul c1).add (hd2.hasFDerivAt.const_mul c2)
        show fderiv ℝ (PartialWord w (fun ζ => c1 * G1 ζ + c2 * G2 ζ)) z
              (if j = 0 then (1 : ℂ) else Complex.I)
            = c1 * fderiv ℝ (PartialWord w G1) z (if j = 0 then (1 : ℂ) else Complex.I)
              + c2 * fderiv ℝ (PartialWord w G2) z (if j = 0 then (1 : ℂ) else Complex.I)
        rw [hev.fderiv_eq, hfd.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
  -- ## Shared tool: the last-letter peel, by `List.foldr_append`
  have hsnoc : ∀ (w' : List (Fin 2)) (j : Fin 2) (G : ℂ → ℂ),
      PartialWord (w' ++ [j]) G = PartialWord w' (PartialWord [j] G) := by
    intro w' j G
    simp only [PartialWord, List.foldr_append]
  -- ## smoothness of `f` and of its conjugate off `z₀`
  have hWo : IsOpen (W \ {z₀}) := hW.sdiff isClosed_singleton
  have hfsm : ContDiffOn ℝ (⊤ : ℕ∞) f (W \ {z₀}) :=
    (hchism.pow n).congr (fun z hz => hfact z hz.1)
  have hcfsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ => starRingEnd ℂ (f ζ)) (W \ {z₀}) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hfsm
  -- ## Step 3: Corollary 2 at the translated data
  have hcor2 : ∃ d0 : ℝ, 0 < d0 ∧ ∃ B0 : ℕ → ℝ, (∀ m, 0 ≤ B0 m) ∧
      ∀ (m : ℕ) (ζ : ℂ), 0 < ‖ζ‖ → ‖ζ‖ < d0 →
        ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) (fun w => f (w + z₀)) ζ‖
          ≤ B0 m * ‖ζ‖ ^ ((n : ℝ) / GammaExp n p - (m : ℝ)) := by
    -- ## Step 2: the translated data
    obtain ⟨Wt, hWtdef⟩ : ∃ S : Set ℂ, S = (fun ζ : ℂ => ζ + z₀) ⁻¹' W := ⟨_, rfl⟩
    have hWtmem : ∀ ζ : ℂ, ζ ∈ Wt ↔ ζ + z₀ ∈ W := by
      intro ζ
      rw [hWtdef]
      exact Iff.rfl
    have hWtopen : IsOpen Wt := by
      rw [hWtdef]
      exact hW.preimage (continuous_add_const z₀)
    have h0Wt : (0 : ℂ) ∈ Wt := by
      rw [hWtmem]
      simpa using hz₀
    -- ### (T): the three transport facts, proved once
    have hmp : MeasureTheory.MeasurePreserving (fun ζ : ℂ => ζ + z₀)
        MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume z₀
    have hae : ∀ q : ℂ → Prop, (∀ᵐ z : ℂ, q z) → ∀ᵐ ζ : ℂ, q (ζ + z₀) :=
      fun q hq => (hmp.quasiMeasurePreserving).ae hq
    have hLp : ∀ (s : ENNReal) (g : ℂ → ℂ), MemLpLocOn s W g →
        MemLpLocOn s Wt (fun ζ => g (ζ + z₀)) := by
      intro s g hg K hKsub hK
      have himg : IsCompact ((fun ζ : ℂ => ζ + z₀) '' K) := hK.image (continuous_add_const z₀)
      have hsub : (fun ζ : ℂ => ζ + z₀) '' K ⊆ W := by
        intro y hy
        obtain ⟨ζ, hζ, rfl⟩ := hy
        exact (hWtmem ζ).mp (hKsub hζ)
      have hid : K.indicator (fun ζ => g (ζ + z₀))
          = fun ζ : ℂ => (((fun ζ : ℂ => ζ + z₀) '' K).indicator g) (ζ + z₀) := by
        funext ζ
        by_cases hζ : ζ ∈ K
        · have hmem2 : ζ + z₀ ∈ (fun ζ : ℂ => ζ + z₀) '' K := ⟨ζ, hζ, rfl⟩
          rw [Set.indicator_of_mem hζ, Set.indicator_of_mem hmem2]
        · have hne : ζ + z₀ ∉ (fun ζ : ℂ => ζ + z₀) '' K := by
            intro hc
            obtain ⟨ζ', hζ', he⟩ := hc
            exact hζ (by rwa [add_right_cancel he] at hζ')
          rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem hne]
      rw [hid]
      exact (hg _ hsub himg).comp_measurePreserving hmp
    have hWP : ∀ (j : Fin 2) (g g' : ℂ → ℂ), IsWeakPartialOn W j g g' →
        IsWeakPartialOn Wt j (fun ζ => g (ζ + z₀)) (fun ζ => g' (ζ + z₀)) := by
      intro j g g' hwp φ hφ
      obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
      have hsupp : tsupport (fun z : ℂ => φ (z - z₀))
          = (Homeomorph.subRight z₀) ⁻¹' tsupport φ := by
        have h1 : (fun z : ℂ => φ (z - z₀)) = φ ∘ (Homeomorph.subRight z₀) := rfl
        rw [h1, tsupport, tsupport, Function.support_comp_eq_preimage,
          ← (Homeomorph.subRight z₀).preimage_closure]
      have hφtest : IsTestFn W (fun z : ℂ => φ (z - z₀)) := by
        refine ⟨hφ1.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
        · have h1 : (fun z : ℂ => φ (z - z₀)) = φ ∘ (Homeomorph.subRight z₀) := rfl
          rw [h1]
          exact hφ2.comp_homeomorph (Homeomorph.subRight z₀)
        · rw [hsupp]
          intro z hz
          have hz' : z - z₀ ∈ tsupport φ := by simpa using hz
          have h2 := (hWtmem (z - z₀)).mp (hφ3 hz')
          simpa using h2
      have hfd : ∀ z : ℂ, fderiv ℝ (fun w : ℂ => φ (w - z₀)) z = fderiv ℝ φ (z - z₀) := by
        intro z
        have h1 : (fun w : ℂ => φ (w - z₀)) = fun w : ℂ => φ (w + -z₀) := by
          funext w
          rw [sub_eq_add_neg]
        rw [h1, fderiv_comp_add_right, ← sub_eq_add_neg]
      have hhyp := hwp (fun z : ℂ => φ (z - z₀)) hφtest
      simp only [hfd] at hhyp
      show (∫ ζ : ℂ, g (ζ + z₀) * fderiv ℝ φ ζ (if j = 0 then (1 : ℂ) else Complex.I))
          = -∫ ζ : ℂ, g' (ζ + z₀) * φ ζ
      have hA : (∫ ζ : ℂ, g (ζ + z₀) * fderiv ℝ φ ζ (if j = 0 then (1 : ℂ) else Complex.I))
          = ∫ z : ℂ, g z * fderiv ℝ φ (z - z₀) (if j = 0 then (1 : ℂ) else Complex.I) := by
        simpa using MeasureTheory.integral_add_right_eq_self
          (fun z : ℂ => g z * fderiv ℝ φ (z - z₀) (if j = 0 then (1 : ℂ) else Complex.I)) z₀
      have hB : (∫ ζ : ℂ, g' (ζ + z₀) * φ ζ) = ∫ z : ℂ, g' z * φ (z - z₀) := by
        simpa using MeasureTheory.integral_add_right_eq_self
          (fun z : ℂ => g' z * φ (z - z₀)) z₀
      rw [hA, hB, hhyp]
    have hWWtrans : ∀ g a b : ℂ → ℂ, IsWeakWirtingerOn W g a b →
        IsWeakWirtingerOn Wt (fun ζ => g (ζ + z₀)) (fun ζ => a (ζ + z₀))
          (fun ζ => b (ζ + z₀)) := by
      intro g a b hww
      obtain ⟨gx, gy, h1, h2, h3, h4, h5, h6, h7⟩ := hww
      exact ⟨fun ζ => gx (ζ + z₀), fun ζ => gy (ζ + z₀),
        hLp 1 g h1, hLp 1 gx h2, hLp 1 gy h3,
        hWP 0 g gx h4, hWP 1 g gy h5,
        fun ζ => h6 (ζ + z₀), fun ζ => h7 (ζ + z₀)⟩
    -- ### (b) the equation
    have h12t : SolvesEq12 p Wt (fun w => f (w + z₀)) := by
      obtain ⟨a12, b12, hww12, heq12⟩ := h12
      refine ⟨fun ζ => a12 (ζ + z₀), fun ζ => b12 (ζ + z₀), hWWtrans _ _ _ hww12, ?_⟩
      filter_upwards [hae _ heq12] with ζ hζ
      intro hmem hne
      exact hζ ((hWtmem ζ).mp hmem) hne
    -- ### (d) quasiconformality
    obtain ⟨hqr, hinjchi, hcontchi, himgopen, psi, hpsi, hpsic⟩ := hqchi
    obtain ⟨hK1, hmw, achi, bchi, hwwchi, hdist⟩ := hqr
    have himgeq : (fun ζ => chi (ζ + z₀)) '' Wt = chi '' W := by
      refine Set.Subset.antisymm ?_ ?_
      · intro y hy
        obtain ⟨ζ, hζ, rfl⟩ := hy
        exact ⟨ζ + z₀, (hWtmem ζ).mp hζ, rfl⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := hy
        refine ⟨z - z₀, ?_, ?_⟩
        · rw [hWtmem]
          simpa using hz
        · simp
    have hmwt : MemWLocOn 1 2 Wt (fun ζ => chi (ζ + z₀)) := by
      obtain ⟨D, hD0, hDL, hDw⟩ := hmw
      refine ⟨fun w => fun ζ => D w (ζ + z₀), ?_, ?_, ?_⟩
      · funext ζ
        show D [] (ζ + z₀) = chi (ζ + z₀)
        rw [hD0]
      · intro w hw
        exact hLp 2 (D w) (hDL w hw)
      · intro w j hw
        exact hWP j (D w) (D (w ++ [j])) (hDw w j hw)
    have hqct : QuasiconformalOn K' Wt (fun ζ => chi (ζ + z₀)) := by
      refine ⟨⟨hK1, hmwt, fun ζ => achi (ζ + z₀), fun ζ => bchi (ζ + z₀),
        hWWtrans _ _ _ hwwchi, ?_⟩, ?_, ?_, ?_, fun w => psi w - z₀, ?_, ?_⟩
      · filter_upwards [hae _ hdist] with ζ hζ
        intro hmem
        exact hζ ((hWtmem ζ).mp hmem)
      · intro ζ1 h1 ζ2 h2 he
        have h3 := hinjchi ((hWtmem ζ1).mp h1) ((hWtmem ζ2).mp h2) he
        exact add_right_cancel h3
      · intro ζ hζ
        exact (hcontchi.comp (Continuous.continuousOn (continuous_add_const z₀))
          (fun ζ' hζ' => (hWtmem ζ').mp hζ')) ζ hζ
      · rw [himgeq]
        exact himgopen
      · intro ζ hζ
        show psi (chi (ζ + z₀)) - z₀ = ζ
        rw [hpsi (ζ + z₀) ((hWtmem ζ).mp hζ)]
        ring
      · rw [himgeq]
        exact hpsic.sub continuousOn_const
    -- ### (c), (e), (f)
    have hf0t : (fun w => f (w + z₀)) 0 = 0 := by simpa using hf0
    have hchi0t : (fun ζ => chi (ζ + z₀)) 0 = 0 := by simpa using hchi0
    have hfactt : ∀ ζ ∈ Wt, f (ζ + z₀) = chi (ζ + z₀) ^ n := by
      intro ζ hζ
      exact hfact (ζ + z₀) ((hWtmem ζ).mp hζ)
    have hchismt : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ => chi (ζ + z₀)) (Wt \ {0}) := by
      refine hchism.comp ((contDiff_id.add contDiff_const).contDiffOn) ?_
      intro ζ hζ
      refine ⟨(hWtmem ζ).mp hζ.1, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hc
      have hz0 : ζ = 0 := by
        have h4 : ζ + z₀ = 0 + z₀ := by simpa using hc
        exact add_right_cancel h4
      exact hζ.2 (by simpa using hz0)
    have hsurjt : ∀ ζ ∈ Wt, (fun w => H w - z₀) (chi (ζ + z₀)) = ζ := by
      intro ζ hζ
      show H (chi (ζ + z₀)) - z₀ = ζ
      rw [hsurj (ζ + z₀) ((hWtmem ζ).mp hζ)]
      ring
    have hHcontt : ContinuousOn (fun w => H w - z₀) ((fun ζ => chi (ζ + z₀)) '' Wt) := by
      rw [himgeq]
      exact hHcont.sub continuousOn_const
    -- ### Step 3: apply Corollary 2
    obtain ⟨d0, hd0, B0, hB0⟩ :=
      Cor2 n p K' hn hp hK' qcp Wt hWtopen h0Wt (fun w => f (w + z₀))
        (fun ζ => chi (ζ + z₀)) (fun w => H w - z₀) h12t hf0t hqct hchi0t hfactt hchismt
        hsurjt hHcontt
    refine ⟨d0, hd0, B0, ?_, hB0⟩
    intro m
    obtain ⟨ζ0, hζ0⟩ : ∃ x : ℂ, x = ((d0 / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
    have hn0 : ‖ζ0‖ = d0 / 2 := by
      rw [hζ0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < d0 / 2)]
    have hpos : (0 : ℝ) < ‖ζ0‖ ^ ((n : ℝ) / GammaExp n p - (m : ℝ)) :=
      Real.rpow_pos_of_pos (by rw [hn0]; linarith) _
    have hle := hB0 m ζ0 (by rw [hn0]; linarith) (by rw [hn0]; linarith)
    have hsum0 : (0 : ℝ) ≤ ∑ v : Fin m → Fin 2,
        ‖PartialWord (List.ofFn v) (fun w => f (w + z₀)) ζ0‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    nlinarith [hsum0, hpos, hle]
  obtain ⟨d0, hd0, B0, hB00, hB0⟩ := hcor2
  -- ## Step 4: the radius, and eliminating `n`
  obtain ⟨δW, hδW, hδWsub⟩ := Metric.isOpen_iff.mp hW z₀ hz₀
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = min (min d0 δW) 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hd0 hδW) one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδd0 : δ ≤ d0 := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδW : δ ≤ δW := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmemW : ∀ z : ℂ, ‖z - z₀‖ < δ → z ∈ W := by
    intro z hz
    refine hδWsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [hδδW]
  have hexp : DExp p ≤ (n : ℝ) / GammaExp n p := by
    rw [hd]
    exact (GammaRatioMinAtOne p hp).2 n hn
  -- (51') : the `n`-free estimate for `f`
  have h51 : ∀ (m : ℕ) (z : ℂ), 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
      ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) f z‖
        ≤ B0 m * ‖z - z₀‖ ^ (DExp p - (m : ℝ)) := by
    intro m z hz1 hz2
    have hball := hB0 m (z - z₀) (by simpa using hz1) (lt_of_lt_of_le hz2 hδd0)
    have hsub : ∀ v : Fin m → Fin 2,
        PartialWord (List.ofFn v) (fun w => f (w + z₀)) (z - z₀)
          = PartialWord (List.ofFn v) f z := by
      intro v
      rw [htrans (List.ofFn v) f]
      simp
    have hrw : ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) (fun w => f (w + z₀)) (z - z₀)‖
        = ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) f z‖ := by
      refine Finset.sum_congr rfl ?_
      intro v _
      rw [hsub v]
    rw [hrw] at hball
    refine le_trans hball ?_
    refine mul_le_mul_of_nonneg_left ?_ (hB00 m)
    refine Real.rpow_le_rpow_of_exponent_ge (by simpa using hz1) (le_trans hz2.le hδ1) ?_
    linarith [hexp]
  -- ## Steps 5 and 6: from (51) to (52), and the constants
  obtain ⟨B, hBdef⟩ : ∃ g : ℕ → ℝ,
      g = fun m => (Fintype.card (Fin (m + 1) → Fin 2) : ℝ) * 2 * B0 m := ⟨_, rfl⟩
  have hcard1 : ∀ m : ℕ, (1 : ℝ) ≤ (Fintype.card (Fin (m + 1) → Fin 2) : ℝ) := by
    intro m
    exact_mod_cast Fintype.card_pos (α := Fin (m + 1) → Fin 2)
  refine ⟨δ, hδ0, hδ1, B, ?_, ?_⟩
  · intro m z hz1 hz2
    refine le_trans (h51 m z hz1 hz2) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
    rw [hBdef]
    nlinarith [hcard1 m, hB00 m]
  · intro m z hz1 hz2
    have hzW : z ∈ W := hmemW z hz2
    have hzne : z ≠ z₀ := by
      intro hc
      rw [hc] at hz1
      simp at hz1
    have hzm : z ∈ W \ {z₀} := ⟨hzW, by simpa using hzne⟩
    -- each summand of the `(m+1)`-sum
    have hterm : ∀ v : Fin (m + 1) → Fin 2,
        ‖PartialWord (List.ofFn v) (fun ζ => ((u ζ : ℝ) : ℂ)) z‖
          ≤ 2 * (B0 m * ‖z - z₀‖ ^ (DExp p - (m : ℝ))) := by
      intro v
      obtain ⟨w', hw'⟩ : ∃ t : List (Fin 2), t = List.ofFn (fun i => v (Fin.castSucc i)) :=
        ⟨_, rfl⟩
      have hofn : List.ofFn v = w' ++ [v (Fin.last m)] := by
        rw [hw', List.ofFn_succ']
        simp [List.concat_eq_append]
      have hw'len : w' = List.ofFn (fun i => v (Fin.castSucc i)) := hw'
      have hbase : ‖PartialWord w' f z‖ ≤ B0 m * ‖z - z₀‖ ^ (DExp p - (m : ℝ)) := by
        refine le_trans ?_ (h51 m z hz1 hz2)
        have hmem := Finset.single_le_sum
          (f := fun v' : Fin m → Fin 2 => ‖PartialWord (List.ofFn v') f z‖)
          (fun v' _ => norm_nonneg _) (Finset.mem_univ (fun i => v (Fin.castSucc i)))
        rw [← hw'len] at hmem
        exact hmem
      rw [hofn, hsnoc]
      by_cases hj : v (Fin.last m) = 0
      · rw [hj]
        have hagree : ∀ ζ ∈ W, PartialWord [(0 : Fin 2)] (fun ζ' => ((u ζ' : ℝ) : ℂ)) ζ
            = (1 : ℂ) * f ζ + (1 : ℂ) * starRingEnd ℂ (f ζ) := by
          intro ζ hζ
          rw [hg0 ζ hζ]
          ring
        rw [hPWcongr w' _ _ W hW hagree z hzW,
          hPWlin w' 1 1 f (fun ζ => starRingEnd ℂ (f ζ)) (W \ {z₀}) hWo hfsm hcfsm z hzm,
          hPWconj w' f]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, norm_one, one_mul, one_mul, RCLike.norm_conj]
        linarith [hbase]
      · have hj1 : v (Fin.last m) = 1 := by omega
        rw [hj1]
        have hagree : ∀ ζ ∈ W, PartialWord [(1 : Fin 2)] (fun ζ' => ((u ζ' : ℝ) : ℂ)) ζ
            = Complex.I * f ζ + (-Complex.I) * starRingEnd ℂ (f ζ) := by
          intro ζ hζ
          rw [hg1 ζ hζ]
          ring
        rw [hPWcongr w' _ _ W hW hagree z hzW,
          hPWlin w' Complex.I (-Complex.I) f (fun ζ => starRingEnd ℂ (f ζ)) (W \ {z₀})
            hWo hfsm hcfsm z hzm,
          hPWconj w' f]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, Complex.norm_I, norm_neg, Complex.norm_I, one_mul, one_mul,
          RCLike.norm_conj]
        linarith [hbase]
    refine le_trans (Finset.sum_le_card_nsmul Finset.univ _
      (2 * (B0 m * ‖z - z₀‖ ^ (DExp p - (m : ℝ)))) (fun v _ => hterm v)) ?_
    simp only [Finset.card_univ, nsmul_eq_mul]
    rw [hBdef]
    refine le_of_eq ?_
    ring
