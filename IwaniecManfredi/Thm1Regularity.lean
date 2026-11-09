import IwaniecManfredi.Thm1DerivBounds
import IwaniecManfredi.Thm1SmoothAcrossZeros
import IwaniecManfredi.PowerIntegrableNearZero
import IwaniecManfredi.WeakGradContinuousRep
import IwaniecManfredi.WeakPartialAcrossPoint
import IwaniecManfredi.NormalizedFactorization
import IwaniecManfredi.KAlphaEqDExpAddOne
import IwaniecManfredi.CGradPackage
import IwaniecManfredi.SmoothOffZeros
import IwaniecManfredi.MemHolderLocOn
import IwaniecManfredi.Lemma2
import IwaniecManfredi.KAlphaWellDefined

/-- The regularity half of Theorem 1: a `p`-harmonic function on a plane
domain has a representative of class `C^{k,α}_loc ∩ W^{k+2,q}_loc`, with
`(k, α)` determined by (9) and `q` in the range (10).  The conclusion is
asserted of a representative, and must be: `PHarmonicOn` sees `u` only through
integrals and so cannot constrain it on a null set, while membership in a
Hölder class can be destroyed by altering a function on one point.  All of
`1 < p < ∞` is covered; only the optimality clause of Theorem 1 excludes
`p = 2`.  The hypotheses are exactly the three quoted results the paper's note
at `paper.tex:103` enumerates: (C1), (C2), (C3).  Section 3's normalisation of
the factorization is not assumed either -- it is derived from those three by
`NormalizedFactorization` -- and the smoothness of the hodograph inverse off
the origin, which earlier cycles tried to assume, is produced downstream by
`Cor1` from the expansion (19) as at `paper.tex:387-388`. -/
theorem Thm1Regularity (p : ℝ) (hp : 1 < p) (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α ≤ 1) (hka : (k : ℝ) + α = KAlphaExp p)
    (cgp : CGradPackage) (qcp : QCPackage) (soz : SmoothOffZeros)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (u : ℂ → ℝ) (hu : PHarmonicOn p Ω u) :
    ∃ w : ℂ → ℝ,
      (∀ᵐ z, z ∈ Ω → w z = u z) ∧
      MemHolderLocOn k α Ω (fun z => ((w z : ℝ) : ℂ)) ∧
      (∀ q : ℝ, 1 ≤ q → q < 2 / (2 - α) →
        MemWLocOn (k + 2) (ENNReal.ofReal q) Ω (fun z => ((w z : ℝ) : ℂ))) := by
  -- ## (1) the bookkeeping: carry the SUM `DExp p + 1 = k + α`, never a `Nat` difference
  have hd1 : DExp p + 1 = (k : ℝ) + α := by rw [← KAlphaEqDExpAddOne p hp, hka]
  -- ## shared tool: reconstruction of an `ℝ`-linear map on `ℂ` from its two values
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ), ∀ (q : ℂ × ℂ) (v : ℂ),
      Θ q v = (v.re : ℂ) * q.1 + (v.im : ℂ) * q.2 := by
    refine ⟨(ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)
      + (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).comp
        (ContinuousLinearMap.snd ℝ ℂ ℂ), ?_⟩
    intro q v
    simp [ContinuousLinearMap.smulRightL_apply_apply, Complex.real_smul]
  have hdecompCLM : ∀ (L : ℂ →L[ℝ] ℂ) (v : ℂ),
      L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
    intro L v
    calc L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := by
          congr 1
          rw [Complex.real_smul, Complex.real_smul, mul_one]
          exact (Complex.re_add_im v).symm
      _ = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
          rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hfin2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  -- ## Step 1: the complex gradient
  obtain ⟨g, hgu, hgg, hg0w, hg1w, hgeq⟩ := id hu
  obtain ⟨f, hfdef⟩ : ∃ G : ℂ → ℂ, G = fun z => (1 / 2 : ℂ) * starRingEnd ℂ (g z) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = max (p - 1) (1 / (p - 1)) := ⟨_, rfl⟩
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    by_cases h2 : (2 : ℝ) ≤ p
    · exact le_max_of_le_left (by linarith)
    · replace h2 : p < 2 := not_le.mp h2
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ hp1]
      nlinarith
  obtain ⟨hfW, hf12, hfqr⟩ := cgp.complex_gradient p Ω u g hΩ hp hu hg0w hg1w
  rw [← hfdef] at hfW hf12 hfqr
  rw [← hKdef] at hfqr
  -- ## Step 2: the continuous representative of the gradient
  obtain ⟨fh, hfhae, hfhcont⟩ := qcp.qr_continuous K Ω f hΩ hfqr
  have h4a : ∀ z : ℂ, (((g z).re : ℝ) : ℂ) = f z + starRingEnd ℂ (f z) := by
    intro z
    simp only [hfdef]
    refine Complex.ext ?_ ?_ <;> (simp; try ring)
  have h4b : ∀ z : ℂ, (((g z).im : ℝ) : ℂ) = Complex.I * (f z - starRingEnd ℂ (f z)) := by
    intro z
    simp only [hfdef]
    refine Complex.ext ?_ ?_ <;> (simp; try ring)
  obtain ⟨Fh, hFhdef⟩ : ∃ G : Fin 2 → ℂ → ℂ, G = fun j =>
      if j = 0 then (fun z => fh z + starRingEnd ℂ (fh z))
      else (fun z => Complex.I * (fh z - starRingEnd ℂ (fh z))) := ⟨_, rfl⟩
  have hFh0 : Fh 0 = fun z => fh z + starRingEnd ℂ (fh z) := by
    simp [hFhdef]
  have hFh1 : Fh 1 = fun z => Complex.I * (fh z - starRingEnd ℂ (fh z)) := by
    simp [hFhdef]
  have hFh0v : ∀ z : ℂ, Fh 0 z = fh z + starRingEnd ℂ (fh z) := by
    intro z; simp [hFhdef]
  have hFh1v : ∀ z : ℂ, Fh 1 z = Complex.I * (fh z - starRingEnd ℂ (fh z)) := by
    intro z; simp [hFhdef]
  have hconjcd : ContDiff ℝ (⊤ : ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have hFhcont : ∀ j : Fin 2, ContinuousOn (Fh j) Ω := by
    intro j
    rcases hfin2 j with hj | hj <;> subst hj
    · rw [hFh0]
      exact hfhcont.add (Complex.continuous_conj.comp_continuousOn hfhcont)
    · rw [hFh1]
      exact continuousOn_const.mul
        (hfhcont.sub (Complex.continuous_conj.comp_continuousOn hfhcont))
  have hFhweak : ∀ j : Fin 2, IsWeakPartialOn Ω j (fun z => ((u z : ℝ) : ℂ)) (Fh j) := by
    intro j φ hφ
    have hzero : ∀ z : ℂ, z ∉ Ω → φ z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun hc => hz (hφ.2.2 hc))
    rcases hfin2 j with hj | hj <;> subst hj
    · have hint : (∫ z, Fh 0 z * φ z) = ∫ z, (((g z).re : ℝ) : ℂ) * φ z := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hfhae] with z hz
        show Fh 0 z * φ z = (((g z).re : ℝ) : ℂ) * φ z
        by_cases hzΩ : z ∈ Ω
        · rw [hFh0v z, h4a z, hz hzΩ]
        · rw [hzero z hzΩ, mul_zero, mul_zero]
      rw [hint]
      exact hg0w φ hφ
    · have hint : (∫ z, Fh 1 z * φ z) = ∫ z, (((g z).im : ℝ) : ℂ) * φ z := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hfhae] with z hz
        show Fh 1 z * φ z = (((g z).im : ℝ) : ℂ) * φ z
        by_cases hzΩ : z ∈ Ω
        · rw [hFh1v z, h4b z, hz hzΩ]
        · rw [hzero z hzΩ, mul_zero, mul_zero]
      rw [hint]
      exact hg1w φ hφ
  have hfhae' : ∀ᵐ z : ℂ, z ∈ Ω → fh z = (1 / 2 : ℂ) * starRingEnd ℂ (g z) := by
    filter_upwards [hfhae] with z hz hzΩ
    rw [hz hzΩ]
    simp only [hfdef]
  obtain ⟨hfhdiff, hfh12⟩ :=
    cgp.complex_gradient_rep p Ω u g fh hΩ hp hu hg0w hg1w hfhae' hfhcont
  -- ## Step 3: `u` is locally integrable
  have hu1 : MemLpLocOn 1 Ω (fun z => ((u z : ℝ) : ℂ)) := by
    intro Kc hKcsub hKc
    refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top
      (hgu Kc hKcsub hKc) ?_ hKc.measure_lt_top.ne ?_
    · intro x hx
      exact Set.indicator_of_notMem hx _
    · rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  -- ## Step 4: the representative
  obtain ⟨w, hwu, hwC1, hwpd⟩ := WeakGradContinuousRep Ω hΩ u Fh hu1 hFhcont hFhweak
  -- ## the restriction engine for `Ω`-indexed weak notions
  have hMLres : ∀ (S : Set ℂ) (s : ENNReal) (v : ℂ → ℂ), S ⊆ Ω →
      MemLpLocOn s Ω v → MemLpLocOn s S v :=
    fun S s v hS h Kc hKsub hKc => h Kc (hKsub.trans hS) hKc
  have htfres : ∀ (S : Set ℂ) (φ : ℂ → ℂ), S ⊆ Ω → IsTestFn S φ → IsTestFn Ω φ :=
    fun S φ hS h => ⟨h.1, h.2.1, h.2.2.trans hS⟩
  have hWPres : ∀ (S : Set ℂ) (j : Fin 2) (v1 v2 : ℂ → ℂ), S ⊆ Ω →
      IsWeakPartialOn Ω j v1 v2 → IsWeakPartialOn S j v1 v2 :=
    fun S j v1 v2 hS h φ hφ => h φ (htfres S φ hS hφ)
  have hres12 : ∀ S : Set ℂ, S ⊆ Ω → SolvesEq12 p S fh := by
    intro S hSΩ
    obtain ⟨a, b, hww, hpt⟩ := hfh12
    obtain ⟨fx, fy, h1, h2, h3, h4, h5, h6, h7⟩ := hww
    exact ⟨a, b, ⟨fx, fy, hMLres S 1 fh hSΩ h1, hMLres S 1 fx hSΩ h2,
      hMLres S 1 fy hSΩ h3, hWPres S 0 fh fx hSΩ h4, hWPres S 1 fh fy hSΩ h5, h6, h7⟩,
      hpt.mono (fun z hz hzS => hz (hSΩ hzS))⟩
  -- ## Step 7's engine: `w` is as smooth as `fh` on any open subset of `Ω`
  have hsmgen : ∀ S : Set ℂ, IsOpen S → S ⊆ Ω → ContDiffOn ℝ (⊤ : ℕ∞) fh S →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((w z : ℝ) : ℂ)) S := by
    intro S hS hSΩ hfhsm
    rw [contDiffOn_infty_iff_fderiv_of_isOpen hS]
    refine ⟨(hwC1.differentiableOn (by simp)).mono hSΩ, ?_⟩
    have h0 : ContDiffOn ℝ (⊤ : ℕ∞) (Fh 0) S := by
      rw [hFh0]; exact hfhsm.add (hconjcd.comp_contDiffOn hfhsm)
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (Fh 1) S := by
      rw [hFh1]
      exact contDiffOn_const.mul (hfhsm.sub (hconjcd.comp_contDiffOn hfhsm))
    refine (Θ.contDiff.comp_contDiffOn (h0.prodMk h1)).congr ?_
    intro x hx
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [Function.comp_apply]
    have e0 : fderiv ℝ (fun z => ((w z : ℝ) : ℂ)) x 1 = Fh 0 x := by
      have h := hwpd 0 x (hSΩ hx); simpa [PartialWord] using h
    have e1 : fderiv ℝ (fun z => ((w z : ℝ) : ℂ)) x Complex.I = Fh 1 x := by
      have h := hwpd 1 x (hSΩ hx); simpa [PartialWord] using h
    rw [hdecompCLM (fderiv ℝ (fun z => ((w z : ℝ) : ℂ)) x) v, e0, e1]
    exact (hΘ (Fh 0 x, Fh 1 x) v).symm
  -- ## Steps 5-8: the singular set, as ONE package covering the degenerate case (`Z = ∅`)
  -- and the nondegenerate case (`Z = Ω ∩ fh⁻¹(0)`) at once
  obtain ⟨Z, hZΩ, hΩZo, hZfin, hsmZ, hrate⟩ : ∃ Z : Set ℂ, Z ⊆ Ω ∧ IsOpen (Ω \ Z) ∧
      (∀ Kc ⊆ Ω, IsCompact Kc → (Z ∩ Kc).Finite) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((w z : ℝ) : ℂ)) (Ω \ Z) ∧
      (∀ z₀ ∈ Z, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ Metric.ball z₀ δ ⊆ Ω ∧
        Metric.ball z₀ δ ∩ Z = {z₀} ∧ ∃ B : ℕ → ℝ, (∀ j : ℕ, 0 ≤ B j) ∧
          ∀ j : ℕ, 1 ≤ j → ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
            ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) (fun ζ => ((w ζ : ℝ) : ℂ)) z‖
              ≤ B j * ‖z - z₀‖ ^ ((k : ℝ) + α - (j : ℝ))) := by
    by_cases hdeg : ∀ z ∈ Ω, fh z = 0
    · -- Step 5: `fh ≡ 0` on `Ω`, so `Z = ∅` works and Step 7 runs on all of `Ω`
      refine ⟨∅, Set.empty_subset _, by rw [Set.sdiff_empty]; exact hΩ,
        fun Kc _ _ => by simp, ?_, by simp⟩
      rw [Set.sdiff_empty]
      exact hsmgen Ω hΩ (subset_refl Ω)
        ((contDiffOn_const (c := (0 : ℂ)) (s := Ω)).congr hdeg)
    · obtain ⟨zs, hzsΩ, hzsne⟩ : ∃ z ∈ Ω, fh z ≠ 0 := by
        by_contra hc
        refine hdeg (fun z hz => ?_)
        by_contra hne
        exact hc ⟨z, hz, hne⟩
      -- (7): the zeros of `fh` are isolated
      have h7 := qcp.qr_discrete_zeros K Ω f fh hΩ hconn hfqr hfhae hfhcont
        ⟨zs, hzsΩ, hzsne⟩
      have hdiffeq : Ω \ (Ω ∩ {z : ℂ | fh z = 0}) = Ω ∩ fh ⁻¹' ({(0 : ℂ)}ᶜ) := by
        ext z
        exact ⟨fun hz => ⟨hz.1, fun hc => hz.2 ⟨hz.1, hc⟩⟩,
          fun hz => ⟨hz.1, fun hc => hz.2 hc.2⟩⟩
      have hZo : IsOpen (Ω \ (Ω ∩ {z : ℂ | fh z = 0})) := by
        rw [hdiffeq]
        exact hfhcont.isOpen_inter_preimage hΩ isOpen_compl_singleton
      refine ⟨Ω ∩ {z : ℂ | fh z = 0}, Set.inter_subset_left, hZo, ?_, ?_, ?_⟩
      · -- (8): local finiteness, by the accumulation-point argument
        intro Kc hKcΩ hKc
        by_contra hfin
        have hinf2 : Set.Infinite ((Ω ∩ {z : ℂ | fh z = 0}) ∩ Kc) := hfin
        obtain ⟨ζ, hζKc, hacc⟩ :=
          hinf2.exists_accPt_of_subset_isCompact hKc (fun x hx => hx.2)
        have hζΩ : ζ ∈ Ω := hKcΩ hζKc
        have hca : ContinuousAt fh ζ := hfhcont.continuousAt (hΩ.mem_nhds hζΩ)
        have hcl : ζ ∈ closure ((Ω ∩ {z : ℂ | fh z = 0}) ∩ Kc) :=
          mem_closure_iff_clusterPt.mpr hacc.clusterPt
        have himg := hca.continuousWithinAt.mem_closure_image hcl
        have hsub : fh '' ((Ω ∩ {z : ℂ | fh z = 0}) ∩ Kc) ⊆ {(0 : ℂ)} := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact hx.1.2
        obtain ⟨r, hr, hrz⟩ := h7 ζ hζΩ
        rw [accPt_iff_nhds] at hacc
        obtain ⟨y, hymem, hyne⟩ :=
          hacc (Metric.ball ζ r) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
        exact hrz y hymem.2.1.1 hyne (Metric.mem_ball.mp hymem.1) hymem.2.1.2
      · -- Step 7: `fh` is `C^∞` off its zero set, hence so is `w`
        refine hsmgen _ hZo Set.sdiff_subset ?_
        refine (soz.smooth_off_zeros p Ω f fh hΩ hp hfW hfhae hfhcont hfhdiff hfh12).mono ?_
        intro z hz
        exact ⟨hz.1, fun hc => hz.2 ⟨hz.1, hc⟩⟩
      · -- Step 8: the estimates at each singular point
        intro z₀ hz₀
        obtain ⟨m, K', V', chi, H, hm, hK'1, hV'o, hz₀V', hV'Ω, hqc, hchi0, hfact, hchism,
          hsurj, hHcont, hH0, hHinv⟩ :=
          NormalizedFactorization p K hp qcp soz Ω hΩ hconn f fh hfqr hfhae hfhcont hfhdiff
            hfh12 ⟨zs, hzsΩ, hzsne⟩ z₀ hz₀.1 hz₀.2
        obtain ⟨δ0, hδ0, hδ01, B, hBf, hBw⟩ :=
          Thm1DerivBounds m p K' hm hp hK'1 qcp z₀ V' hV'o hz₀V' w fh chi H
            (hres12 V' hV'Ω) hz₀.2 hqc hchi0 hfact hchism hsurj hHcont
            (fun z hz => (hwpd 0 z (hV'Ω hz)).trans (hFh0v z))
            (fun z hz => (hwpd 1 z (hV'Ω hz)).trans (hFh1v z))
        have hBnn : ∀ mm : ℕ, 0 ≤ B mm := by
          intro mm
          have hzz : (z₀ + ((δ0 / 2 : ℝ) : ℂ)) - z₀ = ((δ0 / 2 : ℝ) : ℂ) := by ring
          have hzn : ‖(z₀ + ((δ0 / 2 : ℝ) : ℂ)) - z₀‖ = δ0 / 2 := by
            rw [hzz, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by linarith : (0 : ℝ) < δ0 / 2)]
          have h1 := hBw mm (z₀ + ((δ0 / 2 : ℝ) : ℂ)) (by rw [hzn]; linarith)
            (by rw [hzn]; linarith)
          rw [hzn] at h1
          have h2 : (0 : ℝ) ≤ ∑ v : Fin (mm + 1) → Fin 2,
              ‖PartialWord (List.ofFn v) (fun ζ => ((w ζ : ℝ) : ℂ))
                (z₀ + ((δ0 / 2 : ℝ) : ℂ))‖ :=
            Finset.sum_nonneg (fun _ _ => norm_nonneg _)
          have h3 : (0 : ℝ) < (δ0 / 2) ^ (DExp p - (mm : ℝ)) :=
            Real.rpow_pos_of_pos (by linarith) _
          rcases le_or_gt 0 (B mm) with hpos | hneg
          · exact hpos
          · linarith [mul_neg_of_neg_of_pos hneg h3]
        obtain ⟨r, hr, hrz⟩ := h7 z₀ hz₀.1
        obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀.1
        obtain ⟨B', hB'def⟩ : ∃ G : ℕ → ℝ, G = fun j => B (j - 1) := ⟨_, rfl⟩
        refine ⟨min δ0 (min r r'), lt_min hδ0 (lt_min hr hr'),
          le_trans (min_le_left _ _) hδ01, ?_, ?_, B', ?_, ?_⟩
        · intro z hz
          refine hr'sub (Metric.mem_ball.mpr ?_)
          exact lt_of_lt_of_le (Metric.mem_ball.mp hz)
            (le_trans (min_le_right _ _) (min_le_right _ _))
        · refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ?_)
          · by_contra hzne
            refine hrz z hz.2.1 hzne ?_ hz.2.2
            exact lt_of_lt_of_le (Metric.mem_ball.mp hz.1)
              (le_trans (min_le_right _ _) (min_le_left _ _))
          · rw [Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨Metric.mem_ball_self (lt_min hδ0 (lt_min hr hr')), hz₀⟩
        · intro j
          rw [hB'def]
          exact hBnn _
        · intro j hj z hz1 hz2
          obtain ⟨mm, rfl⟩ : ∃ mm : ℕ, j = mm + 1 := ⟨j - 1, by omega⟩
          have hB'v : B' (mm + 1) = B mm := by rw [hB'def]; simp
          have hexp : (k : ℝ) + α - (((mm + 1 : ℕ)) : ℝ) = DExp p - (mm : ℝ) := by
            push_cast
            linarith
          rw [hB'v, hexp]
          exact hBw mm z hz1 (lt_of_lt_of_le hz2 (min_le_left _ _))
  -- ## Step 9: `w` is of class `C^k` on all of `Ω`
  have hCk : ContDiffOn ℝ (k : ℕ) (fun z => ((w z : ℝ) : ℂ)) Ω := by
    refine Thm1SmoothAcrossZeros Ω hΩ Z hZΩ hZfin k hk α hα _ hwC1 hsmZ ?_
    intro z₀ hz₀
    obtain ⟨δ, hδ, hδ1, hballΩ, hballZ, B, hBnn, hBbd⟩ := hrate z₀ hz₀
    exact ⟨δ, hδ, B, fun j hj1 _ z hz1 hz2 => hBbd j hj1 z hz1 hz2⟩
  -- ## Step 10: the Hölder condition on the order-`k` derivative
  have hhold2 : ∀ Kc ⊆ Ω, IsCompact Kc → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Kc, ∀ y ∈ Kc,
      ‖iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω x
        - iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω y‖ ≤ C * ‖x - y‖ ^ α := by
    have hUD : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
    have happ : ∀ (a b : List (Fin 2)) (H : ℂ → ℂ),
        PartialWord (a ++ b) H = PartialWord a (PartialWord b H) := by
      intro a b H
      simp only [PartialWord, List.foldr_append]
    -- ## (10a) part one: the iterated derivative on a basis tuple IS a `PartialWord` derivative
    have hiterPW : ∀ (kk : ℕ) (G : ℂ → ℂ), ContDiffOn ℝ (kk : ℕ) G Ω → ∀ x ∈ Ω,
        ∀ v : Fin kk → Fin 2,
        iteratedFDerivWithin ℝ kk G Ω x (fun i => if v i = 0 then (1 : ℂ) else Complex.I)
          = PartialWord (List.ofFn v) G x := by
      intro kk
      induction kk with
      | zero =>
          intro G _ x _ v
          rw [iteratedFDerivWithin_zero_apply]
          rfl
      | succ kk ih =>
          intro G hG x hx v
          have hfdw : ContDiffOn ℝ (kk : ℕ) (fderivWithin ℝ G Ω) Ω := by
            refine hG.fderivWithin hUD ?_
            rw [show ((kk + 1 : ℕ) : WithTop ℕ∞) = ((kk : ℕ) : WithTop ℕ∞) + 1 from by
              push_cast; ring]
          obtain ⟨gcl, hgcl⟩ : ∃ T : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ, ∀ S : ℂ →L[ℝ] ℂ,
              T S = S (if v (Fin.last kk) = 0 then (1 : ℂ) else Complex.I) :=
            ⟨ContinuousLinearMap.apply ℝ ℂ _, fun _ => rfl⟩
          have hEq : Set.EqOn (PartialWord [v (Fin.last kk)] G)
              ((gcl : (ℂ →L[ℝ] ℂ) → ℂ) ∘ fderivWithin ℝ G Ω) Ω := by
            intro y hy
            show PartialWord [v (Fin.last kk)] G y = gcl (fderivWithin ℝ G Ω y)
            rw [hgcl]
            show fderiv ℝ G y (if v (Fin.last kk) = 0 then (1 : ℂ) else Complex.I)
                = fderivWithin ℝ G Ω y (if v (Fin.last kk) = 0 then (1 : ℂ) else Complex.I)
            rw [fderivWithin_of_isOpen hΩ hy]
          have hgcd : ContDiff ℝ ((kk : ℕ) : WithTop ℕ∞) (fun S : ℂ →L[ℝ] ℂ => gcl S) := gcl.contDiff
          have hcd : ContDiffOn ℝ (kk : ℕ) (PartialWord [v (Fin.last kk)] G) Ω :=
            (hgcd.comp_contDiffOn hfdw).congr hEq
          have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_left gcl
            (hfdw.contDiffWithinAt hx) hUD hx (i := kk) le_rfl
          rw [iteratedFDerivWithin_succ_apply_right hUD hx]
          have h1 := iteratedFDerivWithin_congr (𝕜 := ℝ) hEq hx kk
          have h3 := ih (PartialWord [v (Fin.last kk)] G) hcd x hx
            (fun i : Fin kk => v i.castSucc)
          have hofn : List.ofFn v
              = List.ofFn (fun i : Fin kk => v i.castSucc) ++ [v (Fin.last kk)] := by
            rw [List.ofFn_succ', List.concat_eq_append]
          rw [hofn, happ, ← h3, h1, hcomp]
          simp only [hgcl, ContinuousLinearMap.compContinuousMultilinearMap_coe,
            Function.comp_apply]
          rfl
    -- ## (10a) part two: the multilinear bound by the values on basis tuples
    have hmlbd : ∀ S : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ,
        ‖S‖ ≤ ∑ r : Fin k → Fin 2, ‖S (fun i => if r i = 0 then (1 : ℂ) else Complex.I)‖ := by
      intro S
      refine ContinuousMultilinearMap.opNorm_le_bound
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun m => ?_)
      have h1 : ∀ i : Fin k, m i
          = ∑ j : Fin 2, (if j = 0 then (m i).re else (m i).im)
              • (if j = 0 then (1 : ℂ) else Complex.I) := by
        intro i
        rw [Fin.sum_univ_two]
        norm_num [Complex.real_smul]
      have hm : S m = ∑ r : Fin k → Fin 2,
          (∏ i, (if r i = 0 then (m i).re else (m i).im))
            • S (fun i => if r i = 0 then (1 : ℂ) else Complex.I) := by
        calc S m = S (fun i => ∑ j : Fin 2, (if j = 0 then (m i).re else (m i).im)
                    • (if j = 0 then (1 : ℂ) else Complex.I)) := by
              congr 1
              funext i
              exact h1 i
          _ = ∑ r : Fin k → Fin 2, S (fun i => (if r i = 0 then (m i).re else (m i).im)
                • (if r i = 0 then (1 : ℂ) else Complex.I)) :=
              S.map_sum (fun i j => (if j = 0 then (m i).re else (m i).im)
                • (if j = 0 then (1 : ℂ) else Complex.I))
          _ = _ := by
              refine Finset.sum_congr rfl (fun r _ => ?_)
              exact S.map_smul_univ (fun i => if r i = 0 then (m i).re else (m i).im)
                (fun i => if r i = 0 then (1 : ℂ) else Complex.I)
      rw [hm]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun r _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
      by_cases hj : r i = 0
      · rw [if_pos hj]; exact Complex.abs_re_le_norm _
      · rw [if_neg hj]; exact Complex.abs_im_le_norm _
    -- ## (13): the comparison
    have h13 : ∀ x ∈ Ω, ∀ y ∈ Ω,
        ‖iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω x
          - iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω y‖
          ≤ ∑ v : Fin k → Fin 2, ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) x
              - PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) y‖ := by
      intro x hx y hy
      refine le_trans (hmlbd _) (le_of_eq (Finset.sum_congr rfl (fun r _ => ?_)))
      congr 1
      rw [sub_apply, hiterPW k _ hCk x hx r, hiterPW k _ hCk y hy r]
    -- ## the `Lemma2` transport from `EuclideanSpace ℝ (Fin 2)` to `ℂ`
    have hLemma2C : ∀ ρ : ℝ, 0 < ρ → ∀ (F : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        ContinuousOn F (Metric.ball (0 : ℂ) ρ) →
        ContDiffOn ℝ (1 : ℕ) F (Metric.ball (0 : ℂ) ρ \ {0}) →
        (∀ x ∈ Metric.ball (0 : ℂ) ρ, ‖F x‖ ≤ M * ‖x‖ ^ α) →
        (∀ x ∈ Metric.ball (0 : ℂ) ρ \ {0}, ‖fderiv ℝ F x‖ ≤ M * ‖x‖ ^ (α - 1)) →
        ∀ x ∈ Metric.ball (0 : ℂ) ρ, ∀ y ∈ Metric.ball (0 : ℂ) ρ,
          ‖F x - F y‖ ≤ 5 * M * ‖x - y‖ ^ α := by
      intro ρ hρ F M hM hFc hFd hi hii
      obtain ⟨e, hedef⟩ : ∃ g : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
          g = Complex.orthonormalBasisOneI.repr := ⟨_, rfl⟩
      obtain ⟨iso, hisodef⟩ : ∃ g : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ,
          g = e.symm.toContinuousLinearEquiv := ⟨_, rfl⟩
      have hisoapp : ∀ q : EuclideanSpace ℝ (Fin 2), iso q = e.symm q := by
        intro q; rw [hisodef]; rfl
      have hisocoe : (iso : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ)
          = (e.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) := by
        rw [hisodef]
      have hnorm : ∀ q : EuclideanSpace ℝ (Fin 2), ‖iso q‖ = ‖q‖ := by
        intro q; rw [hisoapp]; exact e.symm.norm_map q
      have hball : ∀ q : EuclideanSpace ℝ (Fin 2),
          q ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ ↔ iso q ∈ Metric.ball (0 : ℂ) ρ := by
        intro q
        rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, hnorm]
      have key := Lemma2 (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) (convex_ball _ _)
        Metric.isOpen_ball (Metric.mem_ball_self hρ) (F ∘ iso) M α hM hα hα1
        (hFc.comp iso.continuous.continuousOn (fun q hq => (hball q).mp hq))
        ?_ ?_ ?_
      · intro x hx y hy
        have h := key (e x) ((hball (e x)).mpr (by rw [hisoapp]; simpa using hx))
          (e y) ((hball (e y)).mpr (by rw [hisoapp]; simpa using hy))
        have hex : (F ∘ iso) (e x) = F x := by
          show F (iso (e x)) = F x
          rw [hisoapp]
          simp
        have hey : (F ∘ iso) (e y) = F y := by
          show F (iso (e y)) = F y
          rw [hisoapp]
          simp
        rw [hex, hey] at h
        refine le_trans h (le_of_eq ?_)
        congr 2
        rw [← e.map_sub, e.norm_map]
      · -- ContDiffOn ℝ 1 (F ∘ iso) (ball 0 ρ \ {0})
        refine hFd.comp (iso.contDiff.contDiffOn) (fun q hq => ?_)
        refine ⟨(hball q).mp hq.1, fun hc => hq.2 ?_⟩
        show q = 0
        rw [← norm_eq_zero, ← hnorm q, hc, norm_zero]
      · intro q hq
        rw [← hnorm q]
        exact hi (iso q) ((hball q).mp hq)
      · intro q hq
        have hq0 : iso q ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
          refine ⟨(hball q).mp hq.1, fun hc => hq.2 ?_⟩
          show q = 0
          rw [← norm_eq_zero, ← hnorm q, hc, norm_zero]
        have hfd : fderiv ℝ (F ∘ iso) q = (fderiv ℝ F (iso q)).comp (iso : _ →L[ℝ] ℂ) :=
          iso.comp_right_fderiv
        rw [← hnorm q, hfd, hisocoe, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
        exact hii (iso q) hq0
    -- ## the word-derivative tools
    have hfwd : ∀ (Sset : Set ℂ), IsOpen Sset → ∀ (G : ℂ → ℂ) (m : ℕ) (t : Fin 2),
        ContDiffOn ℝ ((m + 1 : ℕ)) G Sset → ContDiffOn ℝ (m : ℕ) (PartialWord [t] G) Sset := by
      intro Sset hS G m t hG
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = ((m : ℕ) : WithTop ℕ∞) + 1 from by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen hS] at hG
      exact (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.apply ℝ ℂ
          (if t = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn hG.2.2
    have hwordlow : ∀ (Sset : Set ℂ), IsOpen Sset → ∀ (vv : List (Fin 2)) (m : ℕ) (G : ℂ → ℂ),
        ContDiffOn ℝ ((vv.length + m : ℕ)) G Sset →
        ContDiffOn ℝ (m : ℕ) (PartialWord vv G) Sset := by
      intro Sset hS vv
      induction vv with
      | nil =>
          intro m G h
          have hpe : PartialWord ([] : List (Fin 2)) G = G := rfl
          rw [hpe]
          rw [show ([] : List (Fin 2)).length + m = m from by simp] at h
          exact h
      | cons t vv ih =>
          intro m G h
          rw [show (t :: vv).length + m = vv.length + (m + 1) from by
            simp only [List.length_cons]; omega] at h
          have h2 := ih (m + 1) G h
          rw [show (t :: vv) = [t] ++ vv from rfl, happ]
          exact hfwd Sset hS (PartialWord vv G) m t h2
    have hDcont : ∀ vv : List (Fin 2), vv.length ≤ k →
        ContinuousOn (PartialWord vv (fun z => ((w z : ℝ) : ℂ))) Ω := by
      intro vv hvv
      refine (hwordlow Ω hΩ vv 0 _ ?_).continuousOn
      rw [Nat.add_zero]
      exact hCk.of_le (by exact_mod_cast hvv)
    have hDsm : ∀ vv : List (Fin 2),
        ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord vv (fun z => ((w z : ℝ) : ℂ))) (Ω \ Z) := by
      intro vv
      induction vv with
      | nil => exact hsmZ
      | cons t vv ih =>
          have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
              (fderiv ℝ (PartialWord vv (fun z => ((w z : ℝ) : ℂ)))) (Ω \ Z) :=
            ((contDiffOn_infty_iff_fderiv_of_isOpen hΩZo).mp ih).2
          exact (ContinuousLinearMap.contDiff
            (ContinuousLinearMap.apply ℝ ℂ
              (if t = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
    have hsingle : ∀ (vv : List (Fin 2)) (G : ℂ → ℂ) (z : ℂ),
        ‖PartialWord vv G z‖
          ≤ ∑ uu : Fin vv.length → Fin 2, ‖PartialWord (List.ofFn uu) G z‖ := by
      intro vv G z
      have hofn : List.ofFn (vv.get) = vv := List.ofFn_get vv
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun uu : Fin vv.length → Fin 2 => ‖PartialWord (List.ofFn uu) G z‖)
        (fun uu _ => norm_nonneg _) (Finset.mem_univ vv.get))
      rw [hofn]
    have hopbd : ∀ T : ℂ →L[ℝ] ℂ, ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun z => ?_)
      have hdec : T z = (z.re : ℂ) * T 1 + (z.im : ℂ) * T Complex.I := by
        calc T z = T (z.re • (1 : ℂ) + z.im • Complex.I) := by
              congr 1
              rw [Complex.real_smul, Complex.real_smul, mul_one]
              exact (Complex.re_add_im z).symm
          _ = (z.re : ℂ) * T 1 + (z.im : ℂ) * T Complex.I := by
              rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      rw [hdec]
      refine le_trans (norm_add_le _ _) ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z,
        abs_nonneg z.re, abs_nonneg z.im, norm_nonneg (T 1), norm_nonneg (T Complex.I)]
    have hcons : ∀ (t : Fin 2) (vv : List (Fin 2)) (G : ℂ → ℂ) (z : ℂ),
        PartialWord (t :: vv) G z
          = fderiv ℝ (PartialWord vv G) z (if t = 0 then 1 else Complex.I) :=
      fun _ _ _ _ => rfl
    -- ## the choose-friendly per-point package
    have hrate' : ∀ z₀ : ℂ, ∃ (δ : ℝ) (B : ℕ → ℝ), z₀ ∈ Z →
        (0 < δ ∧ δ ≤ 1 ∧ Metric.ball z₀ δ ⊆ Ω ∧ Metric.ball z₀ δ ∩ Z = {z₀} ∧
          (∀ j : ℕ, 0 ≤ B j) ∧
          ∀ j : ℕ, 1 ≤ j → ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
            ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) (fun ζ => ((w ζ : ℝ) : ℂ)) z‖
              ≤ B j * ‖z - z₀‖ ^ ((k : ℝ) + α - (j : ℝ))) := by
      intro z₀
      by_cases hz₀ : z₀ ∈ Z
      · obtain ⟨δ, h1, h2, h3, h4, B, h5, h6⟩ := hrate z₀ hz₀
        exact ⟨δ, B, fun _ => ⟨h1, h2, h3, h4, h5, h6⟩⟩
      · exact ⟨1, fun _ => 0, fun h => absurd h hz₀⟩
    choose dl Bl hBl using hrate'
    have hsing2 : ∀ (j : ℕ) (u : Fin j → Fin 2) (z : ℂ),
        ‖PartialWord (List.ofFn u) (fun ζ' => ((w ζ' : ℝ) : ℂ)) z‖
          ≤ ∑ u' : Fin j → Fin 2,
              ‖PartialWord (List.ofFn u') (fun ζ' => ((w ζ' : ℝ) : ℂ)) z‖ :=
      fun j u z => Finset.single_le_sum
        (f := fun u' : Fin j → Fin 2 =>
          ‖PartialWord (List.ofFn u') (fun ζ' => ((w ζ' : ℝ) : ℂ)) z‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ u)
    -- ## (10b): the three cases
    intro Kc hKcΩ hKc
    obtain ⟨d0, hd0, hd0sub⟩ := hKc.exists_cthickening_subset_open hΩ hKcΩ
    obtain ⟨r₀, hr₀def⟩ : ∃ y : ℝ, y = d0 / 3 := ⟨_, rfl⟩
    have hr₀ : 0 < r₀ := by rw [hr₀def]; linarith
    have hKc3sub : Metric.cthickening (3 * r₀) Kc ⊆ Ω := by
      rw [show 3 * r₀ = d0 from by rw [hr₀def]; ring]
      exact hd0sub
    have hKc3c : IsCompact (Metric.cthickening (3 * r₀) Kc) := hKc.cthickening
    have hFfin := hZfin _ hKc3sub hKc3c
    obtain ⟨Fs, hFs⟩ : ∃ T : Finset ℂ,
        ∀ z : ℂ, z ∈ T ↔ z ∈ Z ∩ Metric.cthickening (3 * r₀) Kc :=
      ⟨hFfin.toFinset, fun z => hFfin.mem_toFinset⟩
    have hdlpos : ∀ ζ ∈ Fs, 0 < dl ζ := fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).1
    have hdlZ : ∀ ζ ∈ Fs, Metric.ball ζ (dl ζ) ∩ Z = {ζ} :=
      fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.2.2.1
    have hdlsub : ∀ ζ ∈ Fs, Metric.ball ζ (dl ζ) ⊆ Ω :=
      fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.2.1
    have hBlbd : ∀ ζ ∈ Fs, ∀ j : ℕ, 1 ≤ j → ∀ z : ℂ, 0 < ‖z - ζ‖ → ‖z - ζ‖ < dl ζ →
        ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) (fun ζ' => ((w ζ' : ℝ) : ℂ)) z‖
          ≤ Bl ζ j * ‖z - ζ‖ ^ ((k : ℝ) + α - (j : ℝ)) :=
      fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.2.2.2.2
    obtain ⟨d, hd, hdle⟩ : ∃ d : ℝ, 0 < d ∧ ∀ ζ ∈ Fs, d ≤ dl ζ := by
      classical
      rcases Fs.eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, by simp [he]⟩
      · exact ⟨Fs.inf' hne dl, (Finset.lt_inf'_iff hne).mpr hdlpos,
          fun ζ hζ => Finset.inf'_le dl hζ⟩
    obtain ⟨r, hrdef⟩ : ∃ y : ℝ, y = min (min r₀ 1) (d / 8) := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hrdef]; exact lt_min (lt_min hr₀ one_pos) (by linarith)
    have hrr0 : r ≤ r₀ := by rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hr1 : r ≤ 1 := by rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hr4 : ∀ ζ ∈ Fs, 4 * r < dl ζ := by
      intro ζ hζ
      have h1 : r ≤ d / 8 := by rw [hrdef]; exact min_le_right _ _
      have h2 := hdle ζ hζ
      linarith
    obtain ⟨Ms, hMsdef⟩ : ∃ y : ℝ, y = ∑ ζ ∈ Fs, (|Bl ζ k| + |Bl ζ (k + 1)|) := ⟨_, rfl⟩
    have hMs0 : 0 ≤ Ms := by rw [hMsdef]; exact Finset.sum_nonneg (fun ζ _ => by positivity)
    have hMsk : ∀ ζ ∈ Fs, Bl ζ k ≤ Ms ∧ Bl ζ (k + 1) ≤ Ms := by
      intro ζ hζ
      have hle := Finset.single_le_sum (f := fun ζ' : ℂ => |Bl ζ' k| + |Bl ζ' (k + 1)|)
        (fun ζ' _ => by positivity) hζ
      rw [← hMsdef] at hle
      refine ⟨?_, ?_⟩
      · have ha := le_abs_self (Bl ζ k)
        have hb := abs_nonneg (Bl ζ (k + 1))
        linarith
      · have ha := le_abs_self (Bl ζ (k + 1))
        have hb := abs_nonneg (Bl ζ k)
        linarith
    have hTcont : ContinuousOn (iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω) Ω :=
      hCk.continuousOn_iteratedFDerivWithin le_rfl hUD
    obtain ⟨MT, hMT⟩ := hKc.exists_bound_of_continuousOn (hTcont.mono hKcΩ)
    obtain ⟨Sset, hSdef⟩ : ∃ T : Set ℂ,
        T = Metric.cthickening (3 * r₀) Kc ∩ {ξ : ℂ | ∀ ζ ∈ Z, r ≤ ‖ξ - ζ‖} := ⟨_, rfl⟩
    have hSc : IsCompact Sset := by
      rw [hSdef]
      refine hKc3c.inter_right ?_
      have he : {ξ : ℂ | ∀ ζ ∈ Z, r ≤ ‖ξ - ζ‖} = ⋂ ζ ∈ Z, {ξ : ℂ | r ≤ ‖ξ - ζ‖} := by
        ext ξ
        exact ⟨fun h => Set.mem_iInter₂.mpr h, fun h => Set.mem_iInter₂.mp h⟩
      rw [he]
      exact isClosed_biInter (fun ζ _ => isClosed_le continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const)))
    have hSsub : Sset ⊆ Ω \ Z := by
      intro ξ hξ
      rw [hSdef] at hξ
      refine ⟨hKc3sub hξ.1, fun hξZ => ?_⟩
      have h := hξ.2 ξ hξZ
      rw [sub_self, norm_zero] at h
      linarith
    obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ v : Fin k → Fin 2, ∀ ξ ∈ Sset,
        ‖fderiv ℝ (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) ξ‖ ≤ L := by
      have hb : ∀ v : Fin k → Fin 2, ∃ Lv : ℝ, 0 ≤ Lv ∧ ∀ ξ ∈ Sset,
          ‖fderiv ℝ (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) ξ‖ ≤ Lv := by
        intro v
        obtain ⟨Lv, hLv⟩ := hSc.exists_bound_of_continuousOn
          ((((contDiffOn_infty_iff_fderiv_of_isOpen hΩZo).mp
            (hDsm (List.ofFn v))).2).continuousOn.mono hSsub)
        exact ⟨|Lv|, abs_nonneg _, fun ξ hξ => le_trans (hLv ξ hξ) (le_abs_self _)⟩
      choose Lf hLf0 hLfb using hb
      refine ⟨∑ v : Fin k → Fin 2, Lf v, Finset.sum_nonneg (fun _ _ => hLf0 _),
        fun v ξ hξ => le_trans (hLfb v ξ hξ)
          (Finset.single_le_sum (f := Lf) (fun _ _ => hLf0 _) (Finset.mem_univ v))⟩
    obtain ⟨N, hNdef⟩ : ∃ n : ℕ, n = (Finset.univ : Finset (Fin k → Fin 2)).card := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ y : ℝ, y = max (max (2 * |MT| / r ^ α) ((N : ℝ) * (5 * Ms)))
        ((N : ℝ) * (L * r ^ (1 - α))) := ⟨_, rfl⟩
    have hC0 : 0 ≤ C := by
      rw [hCdef]
      refine le_trans ?_ (le_max_left _ _)
      refine le_trans ?_ (le_max_left _ _)
      positivity
    -- Case 2's per-word bound, deferred
    have hper2 : ∀ ζ ∈ Fs, ∀ v : Fin k → Fin 2, ∀ x y : ℂ, ‖x - ζ‖ ≤ 2 * r → ‖x - y‖ < r →
        ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) x
          - PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) y‖ ≤ 5 * Ms * ‖x - y‖ ^ α := by
      intro ζ hζ v x y hζx hxy
      have hζZ : ζ ∈ Z := ((hFs ζ).mp hζ).1
      have h4r : 4 * r < dl ζ := hr4 ζ hζ
      have hdz := hdlpos ζ hζ
      have hmaps : ∀ η : ℂ, η ∈ Metric.ball (0 : ℂ) (4 * r) → η + ζ ∈ Metric.ball ζ (dl ζ) := by
        intro η hη
        rw [Metric.mem_ball, dist_zero_right] at hη
        rw [Metric.mem_ball, dist_eq_norm, show η + ζ - ζ = η from by ring]
        linarith
      have hmapsΩ : ∀ η : ℂ, η ∈ Metric.ball (0 : ℂ) (4 * r) → η + ζ ∈ Ω :=
        fun η hη => hdlsub ζ hζ (hmaps η hη)
      have hmapsΩZ : ∀ η ∈ Metric.ball (0 : ℂ) (4 * r) \ {(0 : ℂ)}, η + ζ ∈ Ω \ Z := by
        intro η hη
        refine ⟨hmapsΩ η hη.1, fun hc => ?_⟩
        have h1 : η + ζ ∈ Metric.ball ζ (dl ζ) ∩ Z := ⟨hmaps η hη.1, hc⟩
        rw [hdlZ ζ hζ, Set.mem_singleton_iff] at h1
        have h2 : η = 0 := by linear_combination h1
        exact hη.2 h2
      -- the order-`k` derivatives vanish at the singular point
      have hPW0 : PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) ζ = 0 := by
        obtain ⟨q, hqdef⟩ : ∃ s : ℕ → ℂ,
            s = fun n : ℕ => ζ + ((dl ζ / ((n : ℝ) + 2) : ℝ) : ℂ) := ⟨_, rfl⟩
        have hqn : ∀ n : ℕ, ‖q n - ζ‖ = dl ζ / ((n : ℝ) + 2) := by
          intro n
          rw [hqdef]
          show ‖ζ + ((dl ζ / ((n : ℝ) + 2) : ℝ) : ℂ) - ζ‖ = dl ζ / ((n : ℝ) + 2)
          rw [show ζ + ((dl ζ / ((n : ℝ) + 2) : ℝ) : ℂ) - ζ
              = ((dl ζ / ((n : ℝ) + 2) : ℝ) : ℂ) from by ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        have hqpos : ∀ n : ℕ, 0 < ‖q n - ζ‖ := by intro n; rw [hqn]; positivity
        have hqlt : ∀ n : ℕ, ‖q n - ζ‖ < dl ζ := by
          intro n
          rw [hqn]
          refine div_lt_self hdz ?_
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have htend0 : Filter.Tendsto (fun n : ℕ => dl ζ / ((n : ℝ) + 2)) Filter.atTop (nhds 0) :=
          Filter.Tendsto.const_div_atTop
            (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop) (dl ζ)
        have hqt : Filter.Tendsto q Filter.atTop (nhds ζ) := by
          have h1 : Filter.Tendsto (fun n : ℕ => ((dl ζ / ((n : ℝ) + 2) : ℝ) : ℂ))
              Filter.atTop (nhds 0) := by
            have h2 := (Complex.continuous_ofReal.tendsto 0).comp htend0
            rw [Complex.ofReal_zero] at h2
            exact h2
          have h3 := Filter.Tendsto.const_add ζ h1
          rw [add_zero] at h3
          rw [hqdef]
          exact h3
        have hca : ContinuousAt (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) ζ :=
          (hDcont (List.ofFn v) (by simp)).continuousAt (hΩ.mem_nhds (hZΩ hζZ))
        have hc1 : Filter.Tendsto
            (fun n => ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) (q n)‖)
            Filter.atTop (nhds ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) ζ‖) :=
          (hca.norm).tendsto.comp hqt
        have hc2 : Filter.Tendsto
            (fun n => ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) (q n)‖)
            Filter.atTop (nhds 0) := by
          refine squeeze_zero' (g := fun n : ℕ => Bl ζ k * ‖q n - ζ‖ ^ α)
            (Filter.Eventually.of_forall (fun n => norm_nonneg _))
            (Filter.Eventually.of_forall (fun n => ?_)) ?_
          · refine le_trans (hsing2 k v (q n)) ?_
            have hb := hBlbd ζ hζ k hk (q n) (hqpos n) (hqlt n)
            rw [show (k : ℝ) + α - (k : ℝ) = α from by ring] at hb
            exact hb
          · have h4 : Filter.Tendsto (fun n : ℕ => ‖q n - ζ‖) Filter.atTop (nhds 0) :=
              htend0.congr (fun n => (hqn n).symm)
            have h5 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h4
            rw [Real.zero_rpow (ne_of_gt hα)] at h5
            simpa using h5.const_mul (Bl ζ k)
        exact norm_eq_zero.mp (tendsto_nhds_unique hc1 hc2)
      -- the `Lemma2` data on the ball of radius `4r`
      have htr : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun η : ℂ => η + ζ) :=
        contDiff_id.add contDiff_const
      have hFc : ContinuousOn (fun η : ℂ => PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))
          (η + ζ)) (Metric.ball (0 : ℂ) (4 * r)) :=
        (hDcont (List.ofFn v) (by simp)).comp
          ((continuous_id.add continuous_const).continuousOn) hmapsΩ
      have hFd : ContDiffOn ℝ (1 : ℕ) (fun η : ℂ =>
          PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) (η + ζ))
          (Metric.ball (0 : ℂ) (4 * r) \ {0}) :=
        ((hDsm (List.ofFn v)).of_le (by simp)).comp htr.contDiffOn hmapsΩZ
      have hi : ∀ η ∈ Metric.ball (0 : ℂ) (4 * r),
          ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) (η + ζ)‖ ≤ Ms * ‖η‖ ^ α := by
        intro η hη
        by_cases h0 : η = 0
        · rw [h0, show (0 : ℂ) + ζ = ζ from by ring, hPW0, norm_zero,
            Real.zero_rpow (ne_of_gt hα), mul_zero]
        · have hnz : 0 < ‖(η + ζ) - ζ‖ := by
            rw [show η + ζ - ζ = η from by ring, norm_pos_iff]
            exact h0
          have hlt2 : ‖(η + ζ) - ζ‖ < dl ζ := by
            rw [show η + ζ - ζ = η from by ring]
            rw [Metric.mem_ball, dist_zero_right] at hη
            linarith
          refine le_trans (hsing2 k v (η + ζ)) ?_
          have hb := hBlbd ζ hζ k hk (η + ζ) hnz hlt2
          rw [show (k : ℝ) + α - (k : ℝ) = α from by ring,
            show η + ζ - ζ = η from by ring] at hb
          exact le_trans hb
            (mul_le_mul_of_nonneg_right (hMsk ζ hζ).1 (Real.rpow_nonneg (norm_nonneg _) _))
      have hii : ∀ η ∈ Metric.ball (0 : ℂ) (4 * r) \ {(0 : ℂ)},
          ‖fderiv ℝ (fun η' : ℂ =>
              PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) (η' + ζ)) η‖
            ≤ Ms * ‖η‖ ^ (α - 1) := by
        intro η hη
        have hηz : η ≠ 0 := fun hc => hη.2 hc
        have hnz : 0 < ‖(η + ζ) - ζ‖ := by
          rw [show η + ζ - ζ = η from by ring, norm_pos_iff]
          exact hηz
        have hlt2 : ‖(η + ζ) - ζ‖ < dl ζ := by
          rw [show η + ζ - ζ = η from by ring]
          have hb := hη.1
          rw [Metric.mem_ball, dist_zero_right] at hb
          linarith
        rw [fderiv_comp_add_right]
        refine le_trans (hopbd _) ?_
        have hofn0 : List.ofFn (Fin.cons (0 : Fin 2) v) = (0 : Fin 2) :: List.ofFn v := by
          rw [List.ofFn_succ]; simp
        have hofn1 : List.ofFn (Fin.cons (1 : Fin 2) v) = (1 : Fin 2) :: List.ofFn v := by
          rw [List.ofFn_succ]; simp
        have e0 : fderiv ℝ (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) (η + ζ) 1
            = PartialWord (List.ofFn (Fin.cons (0 : Fin 2) v))
                (fun z => ((w z : ℝ) : ℂ)) (η + ζ) := by
          rw [hofn0, hcons]; simp
        have e1 : fderiv ℝ (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) (η + ζ)
              Complex.I
            = PartialWord (List.ofFn (Fin.cons (1 : Fin 2) v))
                (fun z => ((w z : ℝ) : ℂ)) (η + ζ) := by
          rw [hofn1, hcons]; simp
        rw [e0, e1]
        have hne : (Fin.cons (0 : Fin 2) v : Fin (k + 1) → Fin 2) ≠ Fin.cons (1 : Fin 2) v := by
          intro hcon
          have h := congrFun hcon 0
          simp at h
        have hps := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ ({Fin.cons (0 : Fin 2) v, Fin.cons (1 : Fin 2) v}
            : Finset (Fin (k + 1) → Fin 2)))
          (fun uu _ _ => norm_nonneg
            (PartialWord (List.ofFn uu) (fun z => ((w z : ℝ) : ℂ)) (η + ζ)))
        rw [Finset.sum_pair hne] at hps
        have hb := hBlbd ζ hζ (k + 1) (by omega) (η + ζ) hnz hlt2
        rw [show η + ζ - ζ = η from by ring,
          show (k : ℝ) + α - (((k + 1 : ℕ)) : ℝ) = α - 1 from by push_cast; ring] at hb
        exact le_trans (le_trans hps hb)
          (mul_le_mul_of_nonneg_right (hMsk ζ hζ).2 (Real.rpow_nonneg (norm_nonneg _) _))
      have hxm : x - ζ ∈ Metric.ball (0 : ℂ) (4 * r) := by
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have hym : y - ζ ∈ Metric.ball (0 : ℂ) (4 * r) := by
        rw [Metric.mem_ball, dist_zero_right]
        have h1 : ‖y - ζ‖ ≤ ‖y - x‖ + ‖x - ζ‖ := by
          rw [show y - ζ = (y - x) + (x - ζ) from by ring]
          exact norm_add_le _ _
        have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
        linarith
      have hfin := hLemma2C (4 * r) (by linarith) _ Ms hMs0 hFc hFd hi hii
        (x - ζ) hxm (y - ζ) hym
      have hfin2 : ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) ((x - ζ) + ζ)
          - PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) ((y - ζ) + ζ)‖
          ≤ 5 * Ms * ‖(x - ζ) - (y - ζ)‖ ^ α := hfin
      rw [show x - ζ + ζ = x from by ring, show y - ζ + ζ = y from by ring,
        show x - ζ - (y - ζ) = x - y from by ring] at hfin2
      exact hfin2
    refine ⟨C, hC0, fun x hx y hy => ?_⟩
    by_cases hxy : x = y
    · subst hxy
      simp [Real.zero_rpow (ne_of_gt hα)]
    have hxy0 : 0 < ‖x - y‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hxy
    have hxyn : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hc1 : r ≤ ‖x - y‖
    · -- Case 1: `T` is bounded on the compact `Kc`
      have hra : (0 : ℝ) < r ^ α := Real.rpow_pos_of_pos hr α
      have hxa : r ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hr.le hc1 hα.le
      have hb : ‖iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω x
          - iteratedFDerivWithin ℝ k (fun z => ((w z : ℝ) : ℂ)) Ω y‖ ≤ 2 * |MT| := by
        refine le_trans (norm_sub_le _ _) ?_
        have h1 := hMT x hx
        have h2 := hMT y hy
        have h3 := le_abs_self MT
        linarith
      have hC1 : 2 * |MT| / r ^ α ≤ C := by
        rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hnn : (0 : ℝ) ≤ 2 * |MT| / r ^ α := by positivity
      have s1 : 2 * |MT| / r ^ α * (r ^ α) ≤ 2 * |MT| / r ^ α * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_left hxa hnn
      have s2 : 2 * |MT| / r ^ α * ‖x - y‖ ^ α ≤ C * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_right hC1 hxyn
      have hkey : 2 * |MT| / r ^ α * (r ^ α) = 2 * |MT| := by field_simp
      rw [hkey] at s1
      linarith
    · have hlt : ‖x - y‖ < r := not_le.mp hc1
      by_cases hc2 : ∃ ζ ∈ Z, ‖x - ζ‖ ≤ 2 * r
      · -- Case 2
        obtain ⟨ζ, hζZ, hζx⟩ := hc2
        have hζFs : ζ ∈ Fs := by
          refine (hFs ζ).mpr ⟨hζZ, ?_⟩
          refine Metric.mem_cthickening_of_dist_le ζ x (3 * r₀) Kc hx ?_
          rw [dist_eq_norm, norm_sub_rev]
          linarith
        refine le_trans (h13 x (hKcΩ hx) y (hKcΩ hy)) ?_
        refine le_trans (Finset.sum_le_sum (fun v _ => hper2 ζ hζFs v x y hζx hlt)) ?_
        rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
        have hC2 : (N : ℝ) * (5 * Ms) ≤ C := by
          rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
        calc (N : ℝ) * (5 * Ms * ‖x - y‖ ^ α)
            = ((N : ℝ) * (5 * Ms)) * ‖x - y‖ ^ α := by ring
          _ ≤ C * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right hC2 hxyn
      · -- Case 3: the whole segment stays at distance `≥ r` from `Z`
        have hfar : ∀ ζ ∈ Z, 2 * r < ‖x - ζ‖ :=
          fun ζ hζ => not_le.mp (fun hcon => hc2 ⟨ζ, hζ, hcon⟩)
        have hseg : ∀ ξ ∈ segment ℝ x y, ξ ∈ Sset := by
          intro ξ hξ
          obtain ⟨a, b, ha, hb, hab, hξe⟩ := hξ
          have hb1 : b ≤ 1 := by linarith
          have hxi : ξ - x = (b : ℂ) * (y - x) := by
            rw [← hξe]
            simp only [Complex.real_smul]
            have hab' : (a : ℂ) + (b : ℂ) = 1 := by
              rw [← Complex.ofReal_add, hab, Complex.ofReal_one]
            linear_combination x * hab'
          have hnb : ‖ξ - x‖ ≤ ‖x - y‖ := by
            rw [hxi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb,
              norm_sub_rev]
            nlinarith [norm_nonneg (x - y)]
          rw [hSdef]
          refine ⟨Metric.mem_cthickening_of_dist_le ξ x (3 * r₀) Kc hx ?_, ?_⟩
          · rw [dist_eq_norm]
            linarith
          · intro ζ hζ
            have h1 := hfar ζ hζ
            have h2 : ‖x - ζ‖ ≤ ‖x - ξ‖ + ‖ξ - ζ‖ := by
              rw [show x - ζ = (x - ξ) + (ξ - ζ) from by ring]
              exact norm_add_le _ _
            have h3 : ‖x - ξ‖ = ‖ξ - x‖ := norm_sub_rev _ _
            linarith
        refine le_trans (h13 x (hKcΩ hx) y (hKcΩ hy)) ?_
        have hper3 : ∀ v : Fin k → Fin 2,
            ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) x
              - PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) y‖
              ≤ L * r ^ (1 - α) * ‖x - y‖ ^ α := by
          intro v
          have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
            (f := PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)))
            (f' := fun ξ => fderiv ℝ (PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ))) ξ)
            (C := L) (s := segment ℝ x y)
            (fun ξ hξ => ((((hDsm (List.ofFn v)).differentiableOn (by simp)).differentiableAt
              (hΩZo.mem_nhds (hSsub (hseg ξ hξ)))).hasFDerivAt).hasFDerivWithinAt)
            (fun ξ hξ => hL v ξ (hseg ξ hξ))
            (convex_segment x y) (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
          have hsplit : ‖x - y‖ = ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) := by
            rw [← Real.rpow_add hxy0]
            norm_num
          have hle2 : ‖x - y‖ ^ (1 - α) ≤ r ^ (1 - α) :=
            Real.rpow_le_rpow (norm_nonneg _) hlt.le (by linarith)
          calc ‖PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) x
                - PartialWord (List.ofFn v) (fun z => ((w z : ℝ) : ℂ)) y‖
              ≤ L * ‖x - y‖ := hmv
            _ = L * (‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α)) := by rw [← hsplit]
            _ = L * ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) := by ring
            _ ≤ L * ‖x - y‖ ^ α * r ^ (1 - α) :=
                mul_le_mul_of_nonneg_left hle2 (by positivity)
            _ = L * r ^ (1 - α) * ‖x - y‖ ^ α := by ring
        refine le_trans (Finset.sum_le_sum (fun v _ => hper3 v)) ?_
        rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
        have hC3 : (N : ℝ) * (L * r ^ (1 - α)) ≤ C := by
          rw [hCdef]; exact le_max_right _ _
        calc (N : ℝ) * (L * r ^ (1 - α) * ‖x - y‖ ^ α)
            = ((N : ℝ) * (L * r ^ (1 - α))) * ‖x - y‖ ^ α := by ring
          _ ≤ C * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right hC3 hxyn
  -- ## Step 11: the Sobolev clause
  have hsob : ∀ q : ℝ, 1 ≤ q → q < 2 / (2 - α) →
      MemWLocOn (k + 2) (ENNReal.ofReal q) Ω (fun z => ((w z : ℝ) : ℂ)) := by
    -- ## word-derivative smoothness transfer, the `hPWcd` and `hwordlow` blocks
    have hfwd : ∀ (S : Set ℂ), IsOpen S → ∀ (G : ℂ → ℂ) (m : ℕ) (t : Fin 2),
        ContDiffOn ℝ ((m + 1 : ℕ)) G S → ContDiffOn ℝ (m : ℕ) (PartialWord [t] G) S := by
      intro S hS G m t hG
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = ((m : ℕ) : WithTop ℕ∞) + 1 from by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen hS] at hG
      exact (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.apply ℝ ℂ
          (if t = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn hG.2.2
    have happ : ∀ (a b : List (Fin 2)) (G : ℂ → ℂ),
        PartialWord (a ++ b) G = PartialWord a (PartialWord b G) := by
      intro a b G
      simp only [PartialWord, List.foldr_append]
    have hwordlow : ∀ (S : Set ℂ), IsOpen S → ∀ (vv : List (Fin 2)) (m : ℕ) (G : ℂ → ℂ),
        ContDiffOn ℝ ((vv.length + m : ℕ)) G S → ContDiffOn ℝ (m : ℕ) (PartialWord vv G) S := by
      intro S hS vv
      induction vv with
      | nil =>
          intro m G h
          have hpe : PartialWord ([] : List (Fin 2)) G = G := rfl
          rw [hpe]
          rw [show ([] : List (Fin 2)).length + m = m from by simp] at h
          exact h
      | cons t vv ih =>
          intro m G h
          rw [show (t :: vv).length + m = vv.length + (m + 1) from by
            simp only [List.length_cons]; omega] at h
          have h2 := ih (m + 1) G h
          rw [show (t :: vv) = [t] ++ vv from rfl, happ]
          exact hfwd S hS (PartialWord vv G) m t h2
    have hDsm : ∀ vv : List (Fin 2),
        ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord vv (fun z => ((w z : ℝ) : ℂ))) (Ω \ Z) := by
      intro vv
      induction vv with
      | nil => exact hsmZ
      | cons t vv ih =>
          have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
              (fderiv ℝ (PartialWord vv (fun z => ((w z : ℝ) : ℂ)))) (Ω \ Z) :=
            ((contDiffOn_infty_iff_fderiv_of_isOpen hΩZo).mp ih).2
          exact (ContinuousLinearMap.contDiff
            (ContinuousLinearMap.apply ℝ ℂ
              (if t = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
    have hDcont : ∀ vv : List (Fin 2), vv.length ≤ k →
        ContinuousOn (PartialWord vv (fun z => ((w z : ℝ) : ℂ))) Ω := by
      intro vv hvv
      refine (hwordlow Ω hΩ vv 0 _ ?_).continuousOn
      rw [Nat.add_zero]
      exact hCk.of_le (by exact_mod_cast hvv)
    -- ## the single-word bound out of the sum over words of a given length
    have hsingle : ∀ (vv : List (Fin 2)) (G : ℂ → ℂ) (z : ℂ),
        ‖PartialWord vv G z‖ ≤ ∑ uu : Fin vv.length → Fin 2, ‖PartialWord (List.ofFn uu) G z‖ := by
      intro vv G z
      have hofn : List.ofFn (vv.get) = vv := List.ofFn_get vv
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun uu : Fin vv.length → Fin 2 => ‖PartialWord (List.ofFn uu) G z‖)
        (fun uu _ => norm_nonneg _) (Finset.mem_univ vv.get))
      rw [hofn]
    -- ## the `MeasureTheory.MemLp` bridge: measurability plus integrability of the `q`-th power
    have hbridge : ∀ (q : ℝ), 0 < q → ∀ f : ℂ → ℝ, MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
        MeasureTheory.Integrable (fun z => ‖f z‖ ^ q) MeasureTheory.volume → MeasureTheory.MemLp f (ENNReal.ofReal q) MeasureTheory.volume := by
      intro q hq0 f hm hi
      refine ⟨hm, ?_⟩
      have h1 : MeasureTheory.eLpNorm (fun z => ‖f z‖ ^ q) 1 MeasureTheory.volume < ⊤ :=
        (MeasureTheory.memLp_one_iff_integrable.mpr hi).2
      rw [MeasureTheory.eLpNorm_norm_rpow f hq0, one_mul] at h1
      by_contra hc
      rw [not_lt, top_le_iff] at hc
      rw [hc, ENNReal.top_rpow_of_pos hq0] at h1
      exact absurd h1 (lt_irrefl _)
    -- ## the choose-friendly form of the per-point package
    have hrate' : ∀ z₀ : ℂ, ∃ (δ : ℝ) (B : ℕ → ℝ), z₀ ∈ Z →
        (0 < δ ∧ δ ≤ 1 ∧ Metric.ball z₀ δ ⊆ Ω ∧ Metric.ball z₀ δ ∩ Z = {z₀} ∧
          (∀ j : ℕ, 0 ≤ B j) ∧
          ∀ j : ℕ, 1 ≤ j → ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
            ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) (fun ζ => ((w ζ : ℝ) : ℂ)) z‖
              ≤ B j * ‖z - z₀‖ ^ ((k : ℝ) + α - (j : ℝ))) := by
      intro z₀
      by_cases hz₀ : z₀ ∈ Z
      · obtain ⟨δ, h1, h2, h3, h4, B, h5, h6⟩ := hrate z₀ hz₀
        exact ⟨δ, B, fun _ => ⟨h1, h2, h3, h4, h5, h6⟩⟩
      · exact ⟨1, fun _ => 0, fun h => absurd h hz₀⟩
    choose dl Bl hBl using hrate'
    -- ## (11a): local `L^q` bounds for every word of length at most `k + 2`
    have h11a : ∀ q : ℝ, 1 ≤ q → q < 2 / (2 - α) → ∀ vv : List (Fin 2), vv.length ≤ k + 2 →
        MemLpLocOn (ENNReal.ofReal q) Ω (PartialWord vv (fun z => ((w z : ℝ) : ℂ))) := by
      intro q hq hq2 vv hvv Kc hKcΩ hKc
      have hq0 : 0 < q := by linarith
      by_cases hvk : vv.length ≤ k
      · -- continuous on `Ω`, hence bounded on the compact `Kc`
        have hcont := hDcont vv hvk
        obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKcΩ)
        refine MeasureTheory.MemLp.of_le
          (MeasureTheory.memLp_indicator_const (ENNReal.ofReal q) hKc.measurableSet M
            (Or.inr hKc.measure_lt_top.ne)) ?_ ?_
        · exact (aestronglyMeasurable_indicator_iff hKc.measurableSet).mpr
            ((hcont.mono hKcΩ).aestronglyMeasurable hKc.measurableSet)
        · refine Filter.Eventually.of_forall (fun z => ?_)
          by_cases hz : z ∈ Kc
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Real.norm_eq_abs]
            exact le_trans (hM z hz) (le_abs_self M)
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
            simp
      · -- `k < |vv| ≤ k + 2`: split `Kc` off the singular balls and into them
        have hvk1 : 1 ≤ vv.length := by omega
        have hF := hZfin Kc hKcΩ hKc
        obtain ⟨Fs, hFs⟩ : ∃ T : Finset ℂ, ∀ z : ℂ, z ∈ T ↔ z ∈ Z ∩ Kc :=
          ⟨hF.toFinset, fun z => hF.mem_toFinset⟩
        have hdlpos : ∀ ζ ∈ Fs, 0 < dl ζ := fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).1
        have hdl1 : ∀ ζ ∈ Fs, dl ζ ≤ 1 := fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.1
        have hBlnn : ∀ ζ ∈ Fs, ∀ j : ℕ, 0 ≤ Bl ζ j :=
          fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.2.2.2.1
        have hBlbd : ∀ ζ ∈ Fs, ∀ j : ℕ, 1 ≤ j → ∀ z : ℂ, 0 < ‖z - ζ‖ → ‖z - ζ‖ < dl ζ →
            ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) (fun ζ' => ((w ζ' : ℝ) : ℂ)) z‖
              ≤ Bl ζ j * ‖z - ζ‖ ^ ((k : ℝ) + α - (j : ℝ)) :=
          fun ζ hζ => (hBl ζ ((hFs ζ).mp hζ).1).2.2.2.2.2
        obtain ⟨U, hUdef⟩ : ∃ S : Set ℂ, S = ⋃ ζ ∈ (Fs : Set ℂ), Metric.ball ζ (dl ζ) := ⟨_, rfl⟩
        have hUo : IsOpen U := by
          rw [hUdef]; exact isOpen_biUnion (fun _ _ => Metric.isOpen_ball)
        obtain ⟨Kc0, hKc0def⟩ : ∃ S : Set ℂ, S = Kc \ U := ⟨_, rfl⟩
        have hKc0c : IsCompact Kc0 := by
          rw [hKc0def, Set.sdiff_eq]
          exact hKc.inter_right hUo.isClosed_compl
        have hKc0sub : Kc0 ⊆ Ω \ Z := by
          intro z hz
          rw [hKc0def] at hz
          refine ⟨hKcΩ hz.1, fun hzZ => hz.2 ?_⟩
          rw [hUdef]
          exact Set.mem_biUnion (Finset.mem_coe.mpr ((hFs z).mpr ⟨hzZ, hz.1⟩))
            (Metric.mem_ball_self (hdlpos z ((hFs z).mpr ⟨hzZ, hz.1⟩)))
        obtain ⟨M, hM⟩ := hKc0c.exists_bound_of_continuousOn
          ((hDsm vv).continuousOn.mono hKc0sub)
        obtain ⟨G, hGdef⟩ : ∃ H : ℂ → ℝ, H = fun z =>
            Kc0.indicator (fun _ => |M|) z
            + ∑ ζ ∈ Fs, (Metric.ball ζ (dl ζ)).indicator
                (fun y => Bl ζ vv.length * ‖y - ζ‖ ^ (α - 2)) z := ⟨_, rfl⟩
        have hsumnn : ∀ z : ℂ, (0 : ℝ) ≤ ∑ ζ ∈ Fs, (Metric.ball ζ (dl ζ)).indicator
            (fun y => Bl ζ vv.length * ‖y - ζ‖ ^ (α - 2)) z :=
          fun z => Finset.sum_nonneg (fun ζ hζ => Set.indicator_nonneg (fun y _ =>
            mul_nonneg (hBlnn ζ hζ _) (Real.rpow_nonneg (norm_nonneg _) _)) z)
        have hind0 : ∀ z : ℂ, (0 : ℝ) ≤ Kc0.indicator (fun _ => |M|) z :=
          fun z => Set.indicator_nonneg (fun _ _ => abs_nonneg M) z
        have hGnn : ∀ z : ℂ, 0 ≤ G z := by
          intro z; rw [hGdef]; exact add_nonneg (hind0 z) (hsumnn z)
        have hGLp : MeasureTheory.MemLp G (ENNReal.ofReal q) MeasureTheory.volume := by
          rw [hGdef]
          refine MeasureTheory.MemLp.add ?_ ?_
          · exact MeasureTheory.memLp_indicator_const _ hKc0c.measurableSet _
              (Or.inr hKc0c.measure_lt_top.ne)
          · refine MeasureTheory.memLp_finsetSum Fs (fun ζ hζ => ?_)
            refine hbridge q hq0 _ ?_ ?_
            · refine (aestronglyMeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr ?_
              exact ((by fun_prop : Measurable
                (fun z : ℂ => Bl ζ vv.length * ‖z - ζ‖ ^ (α - 2))).aestronglyMeasurable).restrict
            · have heq : (fun z : ℂ => ‖(Metric.ball ζ (dl ζ)).indicator
                  (fun y : ℂ => Bl ζ vv.length * ‖y - ζ‖ ^ (α - 2)) z‖ ^ q)
                  = (Metric.ball ζ (dl ζ)).indicator
                    (fun z : ℂ => |Bl ζ vv.length| ^ q * ‖z - ζ‖ ^ ((α - 2) * q)) := by
                funext z
                by_cases hz : z ∈ Metric.ball ζ (dl ζ)
                · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, norm_mul,
                    Real.norm_eq_abs, Real.norm_eq_abs,
                    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (z - ζ)) (α - 2)),
                    Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
                    ← Real.rpow_mul (norm_nonneg _)]
                · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero,
                    Real.zero_rpow (ne_of_gt hq0)]
              rw [heq]
              refine MeasureTheory.IntegrableOn.integrable_indicator ?_ Metric.isOpen_ball.measurableSet
              have hpow := PowerIntegrableNearZero α hα hα1 (dl ζ) (hdlpos ζ hζ) q hq hq2
              have hmp : MeasureTheory.MeasurePreserving (fun z : ℂ => z - ζ) MeasureTheory.volume MeasureTheory.volume :=
                MeasureTheory.measurePreserving_sub_right MeasureTheory.volume ζ
              have hme : MeasurableEmbedding (fun z : ℂ => z - ζ) := measurableEmbedding_subRight ζ
              have hpre : (fun z : ℂ => z - ζ) ⁻¹' Metric.ball (0 : ℂ) (dl ζ)
                  = Metric.ball ζ (dl ζ) := by
                ext z; simp [Metric.mem_ball, dist_eq_norm, sub_zero]
              have htrans : MeasureTheory.IntegrableOn (fun z : ℂ => ‖z - ζ‖ ^ ((α - 2) * q))
                  (Metric.ball ζ (dl ζ)) MeasureTheory.volume := by
                rw [← hpre]
                exact (hmp.integrableOn_comp_preimage hme).mpr hpow
              exact htrans.const_mul _
        have hnull : MeasureTheory.volume (Z ∩ Kc) = 0 := hF.measure_zero MeasureTheory.volume
        have hco : ∀ᵐ z : ℂ, z ∉ Z ∩ Kc := by
          rw [MeasureTheory.ae_iff]
          simpa using hnull
        refine MeasureTheory.MemLp.of_le hGLp ?_ ?_
        · have hmeas : MeasurableSet (Kc \ (Z ∩ Kc)) := hKc.measurableSet.diff hF.measurableSet
          have hsub2 : Kc \ (Z ∩ Kc) ⊆ Ω \ Z :=
            fun z hz => ⟨hKcΩ hz.1, fun hzZ => hz.2 ⟨hzZ, hz.1⟩⟩
          have hm2 : MeasureTheory.AEStronglyMeasurable
              ((Kc \ (Z ∩ Kc)).indicator (PartialWord vv (fun z => ((w z : ℝ) : ℂ)))) MeasureTheory.volume :=
            (aestronglyMeasurable_indicator_iff hmeas).mpr
              (((hDsm vv).continuousOn.mono hsub2).aestronglyMeasurable hmeas)
          refine hm2.congr ?_
          filter_upwards [hco] with z hz
          by_cases hzK : z ∈ Kc
          · have hmem : z ∈ Kc \ (Z ∩ Kc) := ⟨hzK, hz⟩
            rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzK]
          · rw [Set.indicator_of_notMem (fun hc => hzK hc.1), Set.indicator_of_notMem hzK]
        · filter_upwards [hco] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg (hGnn z), hGdef]
          by_cases hzK : z ∈ Kc
          · rw [Set.indicator_of_mem hzK]
            by_cases hz0 : z ∈ Kc0
            · have h1 : Kc0.indicator (fun _ => |M|) z = |M| := Set.indicator_of_mem hz0 _
              have h2 := le_trans (hM z hz0) (le_abs_self M)
              linarith [hsumnn z]
            · have hzU : z ∈ U := by
                rw [hKc0def] at hz0
                by_contra hc
                exact hz0 ⟨hzK, hc⟩
              rw [hUdef] at hzU
              obtain ⟨ζ, hζFs, hzball⟩ := Set.mem_iUnion₂.mp hzU
              have hζm : ζ ∈ Fs := Finset.mem_coe.mp hζFs
              have hznz : 0 < ‖z - ζ‖ := by
                rw [norm_pos_iff]
                refine sub_ne_zero_of_ne (fun hc => hz ?_)
                rw [hc]
                exact (hFs ζ).mp hζm
              have hzd : ‖z - ζ‖ < dl ζ := by
                have h := Metric.mem_ball.mp hzball
                rwa [dist_eq_norm] at h
              have hb1 := hBlbd ζ hζm vv.length hvk1 z hznz hzd
              have hb2 := hsingle vv (fun z => ((w z : ℝ) : ℂ)) z
              have hexp : ‖z - ζ‖ ^ ((k : ℝ) + α - (vv.length : ℝ))
                  ≤ ‖z - ζ‖ ^ (α - 2) := by
                refine Real.rpow_le_rpow_of_exponent_ge hznz
                  (le_trans hzd.le (hdl1 ζ hζm)) ?_
                have hc : (vv.length : ℝ) ≤ (k : ℝ) + 2 := by
                  exact_mod_cast hvv
                linarith
              have hmul : Bl ζ vv.length * ‖z - ζ‖ ^ ((k : ℝ) + α - (vv.length : ℝ))
                  ≤ Bl ζ vv.length * ‖z - ζ‖ ^ (α - 2) :=
                mul_le_mul_of_nonneg_left hexp (hBlnn ζ hζm vv.length)
              have hterm : (Metric.ball ζ (dl ζ)).indicator
                  (fun y => Bl ζ vv.length * ‖y - ζ‖ ^ (α - 2)) z
                  = Bl ζ vv.length * ‖z - ζ‖ ^ (α - 2) := Set.indicator_of_mem hzball _
              have hsum : (Metric.ball ζ (dl ζ)).indicator
                  (fun y => Bl ζ vv.length * ‖y - ζ‖ ^ (α - 2)) z
                  ≤ ∑ ζ' ∈ Fs, (Metric.ball ζ' (dl ζ')).indicator
                      (fun y => Bl ζ' vv.length * ‖y - ζ'‖ ^ (α - 2)) z :=
                Finset.single_le_sum (f := fun ζ' => (Metric.ball ζ' (dl ζ')).indicator
                    (fun y => Bl ζ' vv.length * ‖y - ζ'‖ ^ (α - 2)) z)
                  (fun ζ' hζ' => Set.indicator_nonneg (fun y _ =>
                    mul_nonneg (hBlnn ζ' hζ' _) (Real.rpow_nonneg (norm_nonneg _) _)) z) hζm
              rw [hterm] at hsum
              linarith [hind0 z]
          · rw [Set.indicator_of_notMem hzK, norm_zero]
            exact add_nonneg (hind0 z) (hsumnn z)
    -- ## (11b) and the assembly: the `rev` convention makes the coherence clause a tautology
    intro q hq hq2
    have hq0 : 0 < q := by linarith
    have h1lt : (1 : ℝ) < 2 / (2 - α) := by
      have hd : (0 : ℝ) < 2 - α := by linarith
      obtain ⟨c, hcdef⟩ : ∃ y : ℝ, y = 2 / (2 - α) := ⟨_, rfl⟩
      have hc : c * (2 - α) = 2 := by rw [hcdef]; field_simp
      rw [← hcdef]
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    have hone : ∀ x : ℝ, 0 < x → x ≤ 1 → (1 : ℝ) ≤ x ^ (α - 1) := by
      intro x hx hx1
      have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith : α - 1 ≤ (0 : ℝ))
      rwa [Real.rpow_zero] at h
    refine ⟨fun v => PartialWord v.reverse (fun z => ((w z : ℝ) : ℂ)), rfl, ?_, ?_⟩
    · intro v hv
      exact h11a q hq hq2 v.reverse (by simpa using hv)
    · intro v j hv
      have hrev : (v ++ [j]).reverse = j :: v.reverse := by simp
      show IsWeakPartialOn Ω j (PartialWord v.reverse (fun z => ((w z : ℝ) : ℂ)))
          (PartialWord (v ++ [j]).reverse (fun z => ((w z : ℝ) : ℂ)))
      rw [hrev]
      refine WeakPartialAcrossPoint Ω hΩ Z hZΩ hZfin j
        (PartialWord v.reverse (fun z => ((w z : ℝ) : ℂ)))
        (PartialWord (j :: v.reverse) (fun z => ((w z : ℝ) : ℂ))) (1 - α)
        (by linarith) (by linarith) ((hDsm v.reverse).of_le (by simp)) (fun z _ => rfl) ?_ ?_ ?_
      · have h := h11a 1 le_rfl h1lt v.reverse (by simp; omega)
        rwa [ENNReal.ofReal_one] at h
      · have h := h11a 1 le_rfl h1lt (j :: v.reverse) (by simp; omega)
        rwa [ENNReal.ofReal_one] at h
      · -- the growth bound at each singular point
        intro z₀ hz₀
        obtain ⟨hd0, hd1, hballΩ, hballZ, hBnn0, hBbd0⟩ := hBl z₀ hz₀
        by_cases hvl : v.length = 0
        · -- the word is empty: `w` itself, continuous hence bounded near `z₀`
          have hvnil : v.reverse = [] := by
            have hve : v = [] := List.length_eq_zero_iff.mp hvl
            rw [hve]
            rfl
          have hcb : Metric.closedBall z₀ (dl z₀ / 2) ⊆ Ω := by
            refine subset_trans (fun z hz => ?_) hballΩ
            exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
          obtain ⟨M, hM'⟩ := (isCompact_closedBall z₀ (dl z₀ / 2)).exists_bound_of_continuousOn
            ((hDcont v.reverse (by rw [hvnil]; simp)).mono hcb)
          refine ⟨|M|, dl z₀ / 2, by linarith, fun z hz1 hz2 => ?_⟩
          have hzmem : z ∈ Metric.closedBall z₀ (dl z₀ / 2) := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            linarith
          have hb := hM' z hzmem
          have h1 := hone ‖z - z₀‖ hz1 (by linarith)
          rw [show -(1 - α) = α - 1 from by ring]
          nlinarith [le_abs_self M, abs_nonneg M]
        · -- the word is nonempty: the rate bound at its length
          have hvl1 : 1 ≤ v.reverse.length := by
            rw [List.length_reverse]
            omega
          refine ⟨Bl z₀ v.reverse.length, dl z₀, hd0, fun z hz1 hz2 => ?_⟩
          have hb1 := hBbd0 v.reverse.length hvl1 z hz1 hz2
          have hb2 := hsingle v.reverse (fun z => ((w z : ℝ) : ℂ)) z
          have hexp : ‖z - z₀‖ ^ ((k : ℝ) + α - (v.reverse.length : ℝ))
              ≤ ‖z - z₀‖ ^ (α - 1) := by
            refine Real.rpow_le_rpow_of_exponent_ge hz1 (le_trans hz2.le hd1) ?_
            have hc : (v.reverse.length : ℝ) ≤ (k : ℝ) + 1 := by
              rw [List.length_reverse]
              exact_mod_cast (by omega : v.length ≤ k + 1)
            linarith
          rw [show -(1 - α) = α - 1 from by ring]
          have hmul := mul_le_mul_of_nonneg_left hexp (hBnn0 v.reverse.length)
          linarith
  exact ⟨w, hwu, ⟨hCk, hhold2⟩, hsob⟩
