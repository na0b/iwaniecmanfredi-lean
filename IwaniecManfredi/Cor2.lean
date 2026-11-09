import IwaniecManfredi.ChiHigherDerivBound
import IwaniecManfredi.HodographEq18
import IwaniecManfredi.Eq18ImpliesQuasiregular
import IwaniecManfredi.QCPackage

/-- Corollary 2 of the paper, estimate (48): the derivatives of the complex
gradient `f` of order `m` are `O(|z|^{n/γ_n - m})` near a zero of `f`.  The
hypothesis is the paper's at `paper.tex:474` -- `f` a local solution of (12)
of the form (15) with `f(0) = 0` -- the factorization `f = χ^n` and `χ`'s
quasiconformality coming from the quoted bundle (C2) of `QCPackage`, which
`paper.tex:103` licenses as an explicit hypothesis.  Nothing about `H` beyond
continuity is assumed: equation (18) for it is derived by `HodographEq18`, its
`W^{1,2}_loc` membership, almost-everywhere differentiability and `Jac H > 0`
almost everywhere come from (C2)'s inverse clause, its quasiconformality from
the equation through `Eq18ImpliesQuasiregular`, and its smoothness off the
origin is produced by `Cor1` inside `ChiHigherDerivBound`. -/
theorem Cor2 (n : ℕ) (p : ℝ) (K' : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (hK' : 1 ≤ K')
    (qcp : QCPackage)
    (W : Set ℂ) (hW : IsOpen W) (h0W : (0 : ℂ) ∈ W)
    (f chi H : ℂ → ℂ)
    (h12 : SolvesEq12 p W f) (hf0 : f 0 = 0)
    (hqchi : QuasiconformalOn K' W chi) (hchi0 : chi 0 = 0)
    (hfact : ∀ z ∈ W, f z = chi z ^ n)
    (hchism : ContDiffOn ℝ (⊤ : ℕ∞) chi (W \ {0}))
    (hsurj : ∀ z ∈ W, H (chi z) = z)
    (hHcont : ContinuousOn H (chi '' W))
    :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ → ℝ,
      ∀ (m : ℕ) (z : ℂ), 0 < ‖z‖ → ‖z‖ < δ →
        ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) f z‖
          ≤ B m * ‖z‖ ^ ((n : ℝ) / GammaExp n p - (m : ℝ)) := by
  -- ## Step 0: `γ > 0`
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  -- ## Shared tool: word derivatives of a `C^∞` function are `C^∞`
  have hPWcd : ∀ (w : List (Fin 2)) (u : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) u S → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w u) S := by
    intro w
    induction w with
    | nil => intro u S _ hu; exact hu
    | cons j w ih =>
        intro u S hS hu
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w u) S := ih u S hS hu
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w u)) S :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hS).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  -- ## Shared tool: word derivatives see a function only through an open set
  have hPWcongr : ∀ (w : List (Fin 2)) (u v : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      (∀ z ∈ S, u z = v z) → ∀ z ∈ S, PartialWord w u z = PartialWord w v z := by
    intro w
    induction w with
    | nil => intro u v S _ h z hz; exact h z hz
    | cons j w ih =>
        intro u v S hS h z hz
        have hev : PartialWord w u =ᶠ[nhds z] PartialWord w v := by
          filter_upwards [hS.mem_nhds hz] with ζ hζ using ih u v S hS h ζ hζ
        show fderiv ℝ (PartialWord w u) z _ = fderiv ℝ (PartialWord w v) z _
        rw [hev.fderiv_eq]
  -- ## Shared tool: the triangle inequality for a list sum with a uniform bound
  have hlistnorm : ∀ (g : List (Fin 2) × List (Fin 2) → ℂ)
      (L : List (List (Fin 2) × List (Fin 2))) (C : ℝ), 0 ≤ C →
      (∀ a ∈ L, ‖g a‖ ≤ C) → ‖(L.map g).sum‖ ≤ (L.length : ℝ) * C := by
    intro g L C hC
    induction L with
    | nil => intro _; simp
    | cons a T ih =>
        intro hall
        have h1 : ‖g a‖ ≤ C := hall a (List.mem_cons_self ..)
        have h2 := ih (fun b hb => hall b (List.mem_cons_of_mem _ hb))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine le_trans (norm_add_le _ _) ?_
        push_cast
        linarith
  -- ## Step 1: `V = chi '' W` is an open neighbourhood of `0`
  obtain ⟨hqrchi, hinjchi, hcontchi, hVopen, psi0, hpsi0, hpsi0c⟩ := hqchi
  have h0V : (0 : ℂ) ∈ chi '' W := ⟨0, h0W, hchi0⟩
  -- ## Step 2: `H` is a two-sided inverse between `V` and `W`
  have himg : ∀ ξ ∈ chi '' W, H ξ ∈ W := by
    intro ξ hξ
    obtain ⟨z, hzW, rfl⟩ := hξ
    rw [hsurj z hzW]
    exact hzW
  have hinvV : ∀ ξ ∈ chi '' W, chi (H ξ) = ξ := by
    intro ξ hξ
    obtain ⟨z, hzW, rfl⟩ := hξ
    rw [hsurj z hzW]
  have hH0 : H 0 = 0 := by
    have := hsurj 0 h0W
    rw [hchi0] at this
    exact this
  have hHimgW : H '' (chi '' W) = W := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨ξ, hξ, rfl⟩ := hz
      exact himg ξ hξ
    · intro z hz
      exact ⟨chi z, ⟨z, hz, rfl⟩, hsurj z hz⟩
  have hHmaps : ∀ ξ ∈ chi '' W \ {(0 : ℂ)}, H ξ ∈ W \ {(0 : ℂ)} := by
    intro ξ hξ
    have hξne : ξ ≠ 0 := by simpa using hξ.2
    refine ⟨himg ξ hξ.1, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hc
    exact hξne (by rw [← hinvV ξ hξ.1, hc, hchi0])
  -- ## Step 3: the inverse clauses of (C2), and (18) on `V`
  obtain ⟨hHW, hHdiff, hHJpos⟩ := qcp.qc_inverse K' W chi H hW
    ⟨hqrchi, hinjchi, hcontchi, hVopen, psi0, hpsi0, hpsi0c⟩ hsurj
  have hHJ : ∀ᵐ ξ : ℂ, ξ ∈ chi '' W → Jac H ξ ≠ 0 := by
    filter_upwards [hHJpos] with ξ hξ hmem
    exact ne_of_gt (hξ hmem)
  have h18 : SolvesEq18 n p (chi '' W) H :=
    HodographEq18 n p hn hp W (chi '' W) hW hVopen 0 h0W f chi H hfact hchi0 hinjchi
      hchism hHW hHdiff hHJ himg hinvV hH0 h12
  -- ## Step 5: `H` is `K`-quasiconformal on `V`, with `K = max (p-1) (1/(p-1))`
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK1 : (1 : ℝ) ≤ max (p - 1) (1 / (p - 1)) := by
    by_cases h2 : (2 : ℝ) ≤ p
    · exact le_max_of_le_left (by linarith)
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ hp1]
      nlinarith [not_le.mp h2]
  have hqcH : QuasiconformalOn (max (p - 1) (1 / (p - 1))) (chi '' W) H := by
    refine ⟨Eq18ImpliesQuasiregular p hp n (chi '' W) H hHW h18, ?_, hHcont, ?_,
      chi, hinvV, ?_⟩
    · intro ξ1 h1 ξ2 h2 he
      rw [← hinvV ξ1 h1, ← hinvV ξ2 h2, he]
    · rw [hHimgW]; exact hW
    · rw [hHimgW]; exact hcontchi
  -- ## Step 6: the derivatives of `chi`
  obtain ⟨δ, hδ0, hball, B', hB'0, hB'⟩ :=
    ChiHigherDerivBound n p (max (p - 1) (1 / (p - 1))) hn hp hK1 (chi '' W) (W \ {0})
      hVopen (hW.sdiff isClosed_singleton) h0V H chi hHcont hHdiff hqcH h18 hH0
      hchism hHmaps hinvV
  have hWsub : ∀ z : ℂ, ‖z‖ < δ → z ∈ W := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) δ := by simpa [dist_zero_right] using hz
    have := hball hzb
    rwa [hHimgW] at this
  -- the open set on which every estimate lives
  obtain ⟨G, hGdef⟩ : ∃ S : Set ℂ, S = {z : ℂ | 0 < ‖z‖} ∩ {z : ℂ | ‖z‖ < δ} := ⟨_, rfl⟩
  have hGopen : IsOpen G := by
    rw [hGdef]
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hGmem : ∀ z : ℂ, z ∈ G ↔ (0 < ‖z‖ ∧ ‖z‖ < δ) := by
    intro z
    rw [hGdef]
    exact Iff.rfl
  have hGsub : G ⊆ W \ {(0 : ℂ)} := by
    intro z hz
    obtain ⟨h1, h2⟩ := (hGmem z).mp hz
    refine ⟨hWsub z h2, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun hc => by simp [hc] at h1
  have hchiG : ContDiffOn ℝ (⊤ : ℕ∞) chi G := hchism.mono hGsub
  -- ## Step 7: the Leibniz rule for words, carried as a list of complementary pairs
  have hflatlen : ∀ (j : Fin 2) (L : List (List (Fin 2) × List (Fin 2))),
      (L.flatMap (fun pq => [(j :: pq.1, pq.2), (pq.1, j :: pq.2)])).length = 2 * L.length := by
    intro j L
    induction L with
    | nil => simp
    | cons pq T ih =>
        rw [List.flatMap_cons, List.length_append, ih]
        simp
        ring
  have hflatval : ∀ (u v : ℂ → ℂ) (j : Fin 2) (L : List (List (Fin 2) × List (Fin 2)))
      (z : ℂ),
      (((L.flatMap (fun pq => [(j :: pq.1, pq.2), (pq.1, j :: pq.2)])).map
          (fun pq => PartialWord pq.1 u z * PartialWord pq.2 v z)).sum)
        = (L.map (fun pq => PartialWord (j :: pq.1) u z * PartialWord pq.2 v z
            + PartialWord pq.1 u z * PartialWord (j :: pq.2) v z)).sum := by
    intro u v j L z
    induction L with
    | nil => simp
    | cons pq T ih =>
        rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        ring
  have hprodfd : ∀ (u v : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) u S → ContDiffOn ℝ (⊤ : ℕ∞) v S →
      ∀ (L : List (List (Fin 2) × List (Fin 2))) (z : ℂ), z ∈ S →
        DifferentiableAt ℝ
            (fun ζ => (L.map (fun pq => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ)).sum) z ∧
        ∀ t : ℂ, fderiv ℝ
            (fun ζ => (L.map (fun pq => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ)).sum) z t
          = (L.map (fun pq => fderiv ℝ (PartialWord pq.1 u) z t * PartialWord pq.2 v z
              + PartialWord pq.1 u z * fderiv ℝ (PartialWord pq.2 v) z t)).sum := by
    intro u v S hS hu hv L z hz
    have hdu : ∀ q : List (Fin 2), DifferentiableAt ℝ (PartialWord q u) z := by
      intro q
      exact ((hPWcd q u S hS hu).differentiableOn (by simp)).differentiableAt (hS.mem_nhds hz)
    have hdv : ∀ q : List (Fin 2), DifferentiableAt ℝ (PartialWord q v) z := by
      intro q
      exact ((hPWcd q v S hS hv).differentiableOn (by simp)).differentiableAt (hS.mem_nhds hz)
    induction L with
    | nil =>
        refine ⟨?_, ?_⟩
        · simp
        · intro t
          simp
    | cons pq T ih =>
        obtain ⟨ihd, ihv⟩ := ih
        have hfe : (fun ζ => ((pq :: T).map
              (fun c => PartialWord c.1 u ζ * PartialWord c.2 v ζ)).sum)
            = fun ζ => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ
                + (T.map (fun c => PartialWord c.1 u ζ * PartialWord c.2 v ζ)).sum := by
          funext ζ
          simp
        have h1 : HasFDerivAt (fun ζ => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ)
            (PartialWord pq.1 u z • fderiv ℝ (PartialWord pq.2 v) z
              + PartialWord pq.2 v z • fderiv ℝ (PartialWord pq.1 u) z) z :=
          (hdu pq.1).hasFDerivAt.mul (hdv pq.2).hasFDerivAt
        have h3 : HasFDerivAt (fun ζ => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ
              + (T.map (fun c => PartialWord c.1 u ζ * PartialWord c.2 v ζ)).sum)
            ((PartialWord pq.1 u z • fderiv ℝ (PartialWord pq.2 v) z
              + PartialWord pq.2 v z • fderiv ℝ (PartialWord pq.1 u) z)
              + fderiv ℝ (fun ζ =>
                  (T.map (fun c => PartialWord c.1 u ζ * PartialWord c.2 v ζ)).sum) z) z :=
          h1.add ihd.hasFDerivAt
        rw [hfe]
        refine ⟨h3.differentiableAt, ?_⟩
        intro t
        rw [h3.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [ihv t]
        simp only [List.map_cons, List.sum_cons]
        ring
  have hleib : ∀ (u v : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) u S → ContDiffOn ℝ (⊤ : ℕ∞) v S →
      ∀ w : List (Fin 2), ∃ L : List (List (Fin 2) × List (Fin 2)),
        (∀ pq ∈ L, pq.1.length + pq.2.length = w.length) ∧
        L.length = 2 ^ w.length ∧
        ∀ z ∈ S, PartialWord w (fun t => u t * v t) z
          = (L.map (fun pq => PartialWord pq.1 u z * PartialWord pq.2 v z)).sum := by
    intro u v S hS hu hv w
    induction w with
    | nil =>
        refine ⟨[(([] : List (Fin 2)), ([] : List (Fin 2)))], by simp, by simp, ?_⟩
        intro z _
        simp [PartialWord]
    | cons j w ih =>
        obtain ⟨L, hLdeg, hLlen, hLval⟩ := ih
        refine ⟨L.flatMap (fun pq => [(j :: pq.1, pq.2), (pq.1, j :: pq.2)]), ?_, ?_, ?_⟩
        · intro pq hpq
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hpq
          obtain ⟨pq0, hpq0, h | h⟩ := hpq
          · rw [h]
            simp only [List.length_cons]
            have := hLdeg pq0 hpq0
            omega
          · rw [h]
            simp only [List.length_cons]
            have := hLdeg pq0 hpq0
            omega
        · rw [hflatlen, hLlen]
          simp only [List.length_cons]
          ring
        · intro z hz
          have hdz : PartialWord w (fun t => u t * v t)
              =ᶠ[nhds z] (fun ζ =>
                (L.map (fun pq => PartialWord pq.1 u ζ * PartialWord pq.2 v ζ)).sum) := by
            filter_upwards [hS.mem_nhds hz] with ζ hζ using hLval ζ hζ
          obtain ⟨-, hfv⟩ := hprodfd u v S hS hu hv L z hz
          have hpwb : ∀ (q : List (Fin 2)) (g : ℂ → ℂ) (ζ : ℂ),
              fderiv ℝ (PartialWord q g) ζ (if j = 0 then (1 : ℂ) else Complex.I)
                = PartialWord (j :: q) g ζ := fun _ _ _ => rfl
          show fderiv ℝ (PartialWord w (fun t => u t * v t)) z _ = _
          rw [hdz.fderiv_eq, hfv, hflatval u v j L z]
          simp only [hpwb]
  -- ## Step 8: the derivatives of `chi ^ N`
  have h8 : ∀ N : ℕ, 1 ≤ N → ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ (w : List (Fin 2)) (z : ℂ), z ∈ G →
        ‖PartialWord w (fun t => chi t ^ N) z‖
          ≤ A w.length * ‖z‖ ^ ((N : ℝ) / GammaExp n p - (w.length : ℝ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
        refine ⟨B', hB'0, ?_⟩
        intro w z hzG
        obtain ⟨hz1, hz2⟩ := (hGmem z).mp hzG
        have hfe : (fun t => chi t ^ 1) = chi := by funext t; ring
        rw [hfe]
        have h := hB' w.length w rfl z hz1 hz2
        simpa using h
    | succ N hN ih =>
        obtain ⟨A, hA0, hA⟩ := ih
        refine ⟨fun m => 2 ^ m
          * (∑ ij ∈ Finset.range (m + 1) ×ˢ Finset.range (m + 1), B' ij.1 * A ij.2), ?_, ?_⟩
        · intro m
          refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
          intro ij _
          exact mul_nonneg (hB'0 _) (hA0 _)
        · intro w z hzG
          obtain ⟨hz1, hz2⟩ := (hGmem z).mp hzG
          obtain ⟨L, hLdeg, hLlen, hLval⟩ :=
            hleib chi (fun t => chi t ^ N) G hGopen hchiG (hchiG.pow N) w
          have hfe : (fun t => chi t ^ (N + 1)) = fun t => chi t * chi t ^ N := by
            funext t
            ring
          obtain ⟨Sm, hSm⟩ : ∃ x : ℝ, x =
              ∑ ij ∈ Finset.range (w.length + 1) ×ˢ Finset.range (w.length + 1),
                B' ij.1 * A ij.2 := ⟨_, rfl⟩
          have hSm0 : 0 ≤ Sm := by
            rw [hSm]
            refine Finset.sum_nonneg ?_
            intro ij _
            exact mul_nonneg (hB'0 _) (hA0 _)
          have hdom : ∀ a b : ℕ, a + b = w.length → B' a * A b ≤ Sm := by
            intro a b hab
            rw [hSm]
            have hmem : ((a, b) : ℕ × ℕ)
                ∈ Finset.range (w.length + 1) ×ˢ Finset.range (w.length + 1) := by
              simp only [Finset.mem_product, Finset.mem_range]
              omega
            exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => B' ij.1 * A ij.2)
              (fun ij _ => mul_nonneg (hB'0 _) (hA0 _)) hmem
          have hzp : (0 : ℝ) ≤ ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)) :=
            Real.rpow_nonneg (norm_nonneg _) _
          have hC : ∀ pq ∈ L,
              ‖PartialWord pq.1 chi z * PartialWord pq.2 (fun t => chi t ^ N) z‖
                ≤ Sm * ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)) := by
            intro pq hpq
            have hab := hLdeg pq hpq
            have hb1 := hB' pq.1.length pq.1 rfl z hz1 hz2
            have hb2 := hA pq.2 z hzG
            have hcomb : ‖z‖ ^ (1 / GammaExp n p - (pq.1.length : ℝ))
                * ‖z‖ ^ ((N : ℝ) / GammaExp n p - (pq.2.length : ℝ))
                = ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)) := by
              rw [← Real.rpow_add hz1]
              congr 1
              have hw : ((pq.1.length : ℝ)) + ((pq.2.length : ℝ)) = (w.length : ℝ) := by
                exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hab
              field_simp
              nlinarith [hw]
            rw [norm_mul]
            calc ‖PartialWord pq.1 chi z‖ * ‖PartialWord pq.2 (fun t => chi t ^ N) z‖
                ≤ (B' pq.1.length * ‖z‖ ^ (1 / GammaExp n p - (pq.1.length : ℝ)))
                    * (A pq.2.length * ‖z‖ ^ ((N : ℝ) / GammaExp n p - (pq.2.length : ℝ))) :=
                  mul_le_mul hb1 hb2 (norm_nonneg _)
                    (mul_nonneg (hB'0 _) (Real.rpow_nonneg (norm_nonneg _) _))
              _ = (B' pq.1.length * A pq.2.length)
                    * (‖z‖ ^ (1 / GammaExp n p - (pq.1.length : ℝ))
                      * ‖z‖ ^ ((N : ℝ) / GammaExp n p - (pq.2.length : ℝ))) := by ring
              _ = (B' pq.1.length * A pq.2.length)
                    * ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)) := by rw [hcomb]
              _ ≤ Sm * ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)) :=
                  mul_le_mul_of_nonneg_right (hdom _ _ hab) hzp
          rw [hfe, hLval z hzG]
          have hmain := hlistnorm
            (fun pq => PartialWord pq.1 chi z * PartialWord pq.2 (fun t => chi t ^ N) z) L
            (Sm * ‖z‖ ^ (((N : ℝ) + 1) / GammaExp n p - (w.length : ℝ)))
            (mul_nonneg hSm0 hzp) hC
          rw [hLlen] at hmain
          refine le_trans hmain (le_of_eq ?_)
          simp only [hSm]
          push_cast
          ring
  -- ## Step 9: conclusion
  obtain ⟨A, hA0, hA⟩ := h8 n hn
  refine ⟨δ, hδ0, fun m => 2 ^ m * A m, ?_⟩
  intro m z hz1 hz2
  have hzG : z ∈ G := (hGmem z).mpr ⟨hz1, hz2⟩
  have hzW : z ∈ W := hWsub z hz2
  have hbound : ∀ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) f z‖
      ≤ A m * ‖z‖ ^ ((n : ℝ) / GammaExp n p - (m : ℝ)) := by
    intro v
    have hcg : PartialWord (List.ofFn v) f z
        = PartialWord (List.ofFn v) (fun t => chi t ^ n) z :=
      hPWcongr (List.ofFn v) f (fun t => chi t ^ n) W hW hfact z hzW
    rw [hcg]
    have h := hA (List.ofFn v) z hzG
    rwa [List.length_ofFn] at h
  refine le_trans (Finset.sum_le_card_nsmul Finset.univ _
    (A m * ‖z‖ ^ ((n : ℝ) / GammaExp n p - (m : ℝ))) (fun v _ => hbound v)) ?_
  simp only [Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin m → Fin 2) : ℝ) = 2 ^ m := by
    simp
  rw [hcard]
  exact le_of_eq (by ring)
