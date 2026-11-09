import IwaniecManfredi.Section7Heart
import IwaniecManfredi.ExtremalInverseGradient
import IwaniecManfredi.MemHolderSmallOn
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.PHarmonicOn
import IwaniecManfredi.KAlphaExp
import IwaniecManfredi.KAlphaWellDefined

/-- The optimality half of Theorem 1 (`paper.tex:95-97`): for every
`1 < p < ∞` with `p ≠ 2` and every plane domain `Ω` there is a `p`-harmonic
function on `Ω` lying in neither `C^{k+α}_loc(Ω)` nor
`W^{k+2,2/(2-α)}_loc(Ω)`, with `(k, α)` the pair of (9).  Together with
`Thm1Regularity` this covers `thm:1`; neither node covers it alone.

Three points.  The conclusion is about `v`, whose indices exceed by one those
of (56), which is about `f = v_z`; the shift is made contrapositively, since a
member of `C^{k+α}_loc` has complex gradient in `C^{k-1+α}_loc` and a member
of `W^{k+2,q}_loc` has complex gradient in `W^{k+1,q}_loc`, while the exponent
`q` does not move.  Continuity of `v` is asserted and is not a gratuitous
strengthening: `PHarmonicOn` is invariant under changing `v` on a null set
while membership in a Hölder class is not, so without it the non-membership
clause could be satisfied by editing a function on a null set, and the paper's
own witness -- the potential of the continuous `f` of (55) -- has it.
`IsConnected Ω` carries nonemptiness, without which the claim is false,
and it supplies the point `z₀ ∈ Ω` to which `paper.tex:116` translates the
singular point. -/
theorem Thm1Optimality (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α ≤ 1) (hka : (k : ℝ) + α = KAlphaExp p)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsConnected Ω) :
    ∃ v : ℂ → ℝ,
      PHarmonicOn p Ω v ∧
      ContinuousOn (fun z => ((v z : ℝ) : ℂ)) Ω ∧
      ¬ MemHolderSmallOn k α Ω (fun z => ((v z : ℝ) : ℂ)) ∧
      ¬ MemWLocOn (k + 2) (ENNReal.ofReal (2 / (2 - α))) Ω
        (fun z => ((v z : ℝ) : ℂ)) := by
  -- carry the successor, never the difference: `k = m + 1` with `m = k - 1`
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  -- ## Step 1: the extremal data
  obtain ⟨f, v₀, hfcont, hfH, hHf, hfsm, hhom1, hhom2, hv₀cont, hv₀sm, hph₀, hvpot⟩ :=
    ExtremalInverseGradient p hp
  -- ## Step 2: translate the singular point into `Ω`
  obtain ⟨z₀, hz₀⟩ := hconn.nonempty
  obtain ⟨U, hUdef⟩ : ∃ S : Set ℂ, S = {z : ℂ | z + z₀ ∈ Ω} := ⟨_, rfl⟩
  have hUmem : ∀ z : ℂ, z ∈ U ↔ z + z₀ ∈ Ω := by
    intro z
    rw [hUdef]
    exact Iff.rfl
  have hUopen : IsOpen U := by
    have heq : U = (fun y : ℂ => y + z₀) ⁻¹' Ω := by
      ext z
      rw [hUmem z]
      exact Iff.rfl
    rw [heq]
    exact hΩ.preimage (continuous_id.add continuous_const)
  have hU0 : (0 : ℂ) ∈ U := by
    rw [hUmem]
    simpa using hz₀
  -- ## Step 3: (56) on `U`
  obtain ⟨hnoH, hnoW⟩ := Section7Heart p hp hp2 (m + 1) α hk hα hα1 hka U hUopen hU0 f
    hfsm hfH hHf hhom1 hhom2
  simp only [Nat.add_sub_cancel] at hnoH hnoW
  -- ## Step 4b: the three translation transfers
  -- a test function for `B` pulls back to one for `A`
  have htest : ∀ (c : ℂ) (A B : Set ℂ), (∀ z : ℂ, z ∈ B → z - c ∈ A) →
      ∀ φ : ℂ → ℂ, IsTestFn B φ → IsTestFn A (fun ζ => φ (ζ + c)) := by
    intro c A B hrel φ hφ
    refine ⟨hφ.1.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
    · have h := hφ.2.1.comp_homeomorph (Homeomorph.addRight c)
      exact h
    · -- the support translates
      have hsupp : Function.support (fun ζ => φ (ζ + c)) = (fun ζ : ℂ => ζ + c) ⁻¹'
          Function.support φ := by
        ext ζ
        simp only [Function.mem_support, Set.mem_preimage]
      have htsupp : tsupport (fun ζ => φ (ζ + c)) = (fun ζ : ℂ => ζ + c) ⁻¹' tsupport φ := by
        rw [tsupport, tsupport, hsupp]
        exact ((Homeomorph.addRight c).preimage_closure _).symm
      intro ζ hζ
      rw [htsupp] at hζ
      have h1 : ζ + c ∈ B := hφ.2.2 hζ
      have h2 : (ζ + c) - c ∈ A := hrel (ζ + c) h1
      simpa using h2
  -- local `Lᵖ` membership transfers
  have hLp : ∀ (c : ℂ) (A B : Set ℂ) (s : ENNReal) (u : ℂ → ℂ),
      (∀ z : ℂ, z ∈ B → z - c ∈ A) → MemLpLocOn s A u →
      MemLpLocOn s B (fun z => u (z - c)) := by
    intro c A B s u hrel hu K hKB hK
    obtain ⟨K', hK'def⟩ : ∃ S : Set ℂ, S = (fun z : ℂ => z - c) '' K := ⟨_, rfl⟩
    have hK'c : IsCompact K' := by
      rw [hK'def]
      exact hK.image (continuous_id.sub continuous_const)
    have hK'A : K' ⊆ A := by
      rw [hK'def]
      rintro x ⟨z, hz, rfl⟩
      exact hrel z (hKB hz)
    have hmemK : ∀ z : ℂ, z ∈ K ↔ z - c ∈ K' := by
      intro z
      rw [hK'def]
      constructor
      · intro hz
        exact ⟨z, hz, rfl⟩
      · rintro ⟨y, hy, hyz⟩
        have : y = z := by
          have := hyz
          linear_combination this
        rwa [this] at hy
    have heqind : (K.indicator (fun z => u (z - c)))
        = (fun z : ℂ => (K'.indicator u) (z - c)) := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hmemK z).mp hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun hc => hz ((hmemK z).mpr hc))]
    rw [heqind]
    have hmp : MeasureTheory.MeasurePreserving (fun z : ℂ => z - c)
        MeasureTheory.volume MeasureTheory.volume := by
      have h := MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-c)
      simpa [sub_eq_add_neg] using h
    exact (hu K' hK'A hK'c).comp_measurePreserving hmp
  -- weak partial derivatives transfer
  have hWP : ∀ (c : ℂ) (A B : Set ℂ) (j : Fin 2) (u w : ℂ → ℂ),
      (∀ z : ℂ, z ∈ B → z - c ∈ A) → IsWeakPartialOn A j u w →
      IsWeakPartialOn B j (fun z => u (z - c)) (fun z => w (z - c)) := by
    intro c A B j u w hrel hwp φ hφ
    have h := hwp (fun ζ => φ (ζ + c)) (htest c A B hrel φ hφ)
    have hfd : ∀ z : ℂ, fderiv ℝ (fun ζ => φ (ζ + c)) (z - c) = fderiv ℝ φ z := by
      intro z
      rw [fderiv_comp_add_right]
      congr 1
      ring
    show ∫ z : ℂ, u (z - c) * fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I)
      = -∫ z : ℂ, w (z - c) * φ z
    have h1 : ∫ z : ℂ, u (z - c) * fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I)
        = ∫ ζ : ℂ, u ζ *
            fderiv ℝ (fun y => φ (y + c)) ζ (if j = 0 then (1 : ℂ) else Complex.I) := by
      rw [← MeasureTheory.integral_sub_right_eq_self
        (fun ζ : ℂ => u ζ * fderiv ℝ (fun y => φ (y + c)) ζ
          (if j = 0 then (1 : ℂ) else Complex.I)) c]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro z
      simp only
      rw [hfd z]
    have h2 : ∫ z : ℂ, w (z - c) * φ z = ∫ ζ : ℂ, w ζ * φ (ζ + c) := by
      rw [← MeasureTheory.integral_sub_right_eq_self (fun ζ : ℂ => w ζ * φ (ζ + c)) c]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro z
      simp only
      congr 2
      ring
    rw [h1, h2]
    exact h
  refine ⟨fun z => v₀ (z - z₀), ?_, ?_, ?_, ?_⟩
  · -- ## Step 5: (a), `p`-harmonicity on `Ω`
    obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ := hph₀
    have hrelu : ∀ z : ℂ, z ∈ Ω → z - z₀ ∈ (Set.univ : Set ℂ) := fun z _ => Set.mem_univ _
    refine ⟨fun z => g (z - z₀), ?_, ?_, ?_, ?_, ?_⟩
    · exact hLp z₀ Set.univ Ω (ENNReal.ofReal p) (fun z => ((v₀ z : ℝ) : ℂ)) hrelu hg1
    · exact hLp z₀ Set.univ Ω (ENNReal.ofReal p) g hrelu hg2
    · exact hWP z₀ Set.univ Ω 0 (fun z => ((v₀ z : ℝ) : ℂ))
        (fun z => (((g z).re : ℝ) : ℂ)) hrelu hg3
    · exact hWP z₀ Set.univ Ω 1 (fun z => ((v₀ z : ℝ) : ℂ))
        (fun z => (((g z).im : ℝ) : ℂ)) hrelu hg4
    · intro φ hφ
      have hψ : IsTestFn (Set.univ : Set ℂ) (fun ζ => ((φ (ζ + z₀) : ℝ) : ℂ)) :=
        htest z₀ Set.univ Ω hrelu (fun z => ((φ z : ℝ) : ℂ)) hφ
      have h := hg5 (fun ζ => φ (ζ + z₀)) hψ
      have hfd : ∀ z : ℂ, fderiv ℝ (fun ζ => φ (ζ + z₀)) (z - z₀) = fderiv ℝ φ z := by
        intro z
        rw [fderiv_comp_add_right]
        congr 1
        ring
      rw [← MeasureTheory.integral_sub_right_eq_self
        (fun ζ : ℂ => ‖g ζ‖ ^ (p - 2) *
          (g ζ * starRingEnd ℂ
            (((fderiv ℝ (fun y => φ (y + z₀)) ζ 1 : ℝ) : ℂ)
              + Complex.I * ((fderiv ℝ (fun y => φ (y + z₀)) ζ Complex.I : ℝ) : ℂ))).re) z₀] at h
      refine Eq.trans ?_ h
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro z
      simp only
      rw [hfd z]
  · -- ## Step 5: (b), continuity on `Ω`
    exact ((Complex.continuous_ofReal.comp hv₀cont).comp
      (continuous_id.sub continuous_const)).continuousOn
  · -- ## Step 6: (c)
    intro H
    have hcast : ((m : ℕ) : WithTop ℕ∞) + 1 = (((m + 1) : ℕ) : WithTop ℕ∞) := by
      rw [show ((1 : WithTop ℕ∞)) = ((1 : ℕ) : WithTop ℕ∞) by norm_num, ← Nat.cast_add]
    have hUunique : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn
    have hmaps : Set.MapsTo (fun z : ℂ => z + z₀) U Ω := fun z hz => (hUmem z).mp hz
    -- the translated derivative identity
    have himg : (fun y : ℂ => -z₀ + y) '' Ω = U := by
      ext z
      simp only [Set.mem_image]
      rw [hUmem z]
      constructor
      · rintro ⟨y, hy, hyz⟩
        have hy' : y = z + z₀ := by linear_combination hyz
        rwa [hy'] at hy
      · intro h
        exact ⟨z + z₀, h, by ring⟩
    have hvadd : ∀ (n : ℕ) (x : ℂ),
        iteratedFDerivWithin ℝ n (fun z => ((v₀ (z - z₀) : ℝ) : ℂ)) Ω x
          = iteratedFDerivWithin ℝ n (fun z => ((v₀ z : ℝ) : ℂ))
              ((fun y : ℂ => -z₀ + y) '' Ω) (x - z₀) := by
      intro n x
      have h := iteratedFDerivWithin_comp_sub (𝕜 := ℝ)
        (f := fun z : ℂ => ((v₀ z : ℝ) : ℂ)) (s := Ω) (x := x) n z₀
      rw [← Set.image_vadd] at h
      simp only [vadd_eq_add] at h
      exact h
    have hder : ∀ (n : ℕ) (x : ℂ),
        iteratedFDerivWithin ℝ n (fun z => ((v₀ (z - z₀) : ℝ) : ℂ)) Ω (x + z₀)
          = iteratedFDerivWithin ℝ n (fun z => ((v₀ z : ℝ) : ℂ)) U x := by
      intro n x
      rw [hvadd n (x + z₀), himg]
      congr 1
      ring
    -- the `C^m` transfer
    have hCtrans : ∀ (m : ℕ), ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
        (fun z => ((v₀ (z - z₀) : ℝ) : ℂ)) Ω →
        ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun z => ((v₀ z : ℝ) : ℂ)) U := by
      intro m hC
      have hcomp := hC.comp ((contDiff_id.add contDiff_const).contDiffOn) hmaps
      refine hcomp.congr ?_
      intro z hz
      have hid : id z + z₀ - z₀ = z := by simp
      simp only [Function.comp_apply, hid]
    -- Step 6's transfer of the Hölder class to `U`
    have hH' : MemHolderSmallOn (m + 1) α U (fun z => ((v₀ z : ℝ) : ℂ)) := by
      rcases H with ⟨hα1', hC⟩ | ⟨hαlt, hC, hlo⟩
      · exact Or.inl ⟨hα1', by
          have h := hCtrans ((m + 1) + 1) (by
            have hc2 : (((m + 1) : ℕ) : WithTop ℕ∞) + 1 = (((m + 1) + 1 : ℕ) : WithTop ℕ∞) := by
              rw [show ((1 : WithTop ℕ∞)) = ((1 : ℕ) : WithTop ℕ∞) by norm_num, ← Nat.cast_add]
            rw [← hc2]
            exact hC)
          have hc2 : (((m + 1) : ℕ) : WithTop ℕ∞) + 1 = (((m + 1) + 1 : ℕ) : WithTop ℕ∞) := by
            rw [show ((1 : WithTop ℕ∞)) = ((1 : ℕ) : WithTop ℕ∞) by norm_num, ← Nat.cast_add]
          rw [hc2]
          exact h⟩
      · refine Or.inr ⟨hαlt, hCtrans (m + 1) hC, ?_⟩
        intro K hKU hK δ hδ
        obtain ⟨ρ, hρ, hb⟩ := hlo ((fun z : ℂ => z + z₀) '' K)
          (fun x hx => by
            obtain ⟨z, hz, rfl⟩ := hx
            exact (hUmem z).mp (hKU hz))
          (hK.image (continuous_id.add continuous_const)) δ hδ
        refine ⟨ρ, hρ, ?_⟩
        intro x hx y hy hxy
        have hx' : x + z₀ ∈ (fun z : ℂ => z + z₀) '' K := ⟨x, hx, rfl⟩
        have hy' : y + z₀ ∈ (fun z : ℂ => z + z₀) '' K := ⟨y, hy, rfl⟩
        have hxy' : ‖(x + z₀) - (y + z₀)‖ < ρ := by
          rw [show (x + z₀) - (y + z₀) = x - y by ring]
          exact hxy
        have h := hb (x + z₀) hx' (y + z₀) hy' hxy'
        rw [hder (m + 1) x, hder (m + 1) y, show (x + z₀) - (y + z₀) = x - y by ring] at h
        exact h
    -- the Wirtinger operator as a continuous linear map on differentials
    obtain ⟨T, hTdef⟩ : ∃ L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ, L =
        (1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ))
          - Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I)) := ⟨_, rfl⟩
    have hTapp : ∀ A : ℂ →L[ℝ] ℂ, T A = (1 / 2 : ℂ) * (A 1 - Complex.I * A Complex.I) := by
      intro A
      rw [hTdef]
      simp only [smul_apply, sub_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
    have hDZT : ∀ (g : ℂ → ℂ) (z : ℂ), DZ g z = T (fderiv ℝ g z) := by
      intro g z
      rw [hTapp]
      unfold DZ
      rfl
    -- `v₀` is at least `C^(m + 1)` on `U` in both cases of the Hölder class
    have hVk : ContDiffOn ℝ (((m + 1) : ℕ) : WithTop ℕ∞) (fun z => ((v₀ z : ℝ) : ℂ)) U := by
      rcases hH' with ⟨-, hC⟩ | ⟨-, hC, -⟩
      · refine hC.of_le ?_
        rw [show ((1 : WithTop ℕ∞)) = ((1 : ℕ) : WithTop ℕ∞) by norm_num, ← Nat.cast_add]
        exact_mod_cast Nat.le_succ (m + 1)
      · exact hC
    have hfdC : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
        (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U := by
      refine hVk.fderiv_of_isOpen hUopen ?_
      rw [hcast]
    have hw₀cont : ContinuousOn (fun z => T (fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z)) U := by
      have h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
          (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U := by
        refine hVk.fderiv_of_isOpen hUopen ?_
        have h1 : ((0 : ℕ) : WithTop ℕ∞) + 1 = ((1 : ℕ) : WithTop ℕ∞) := by norm_num
        rw [h1]
        exact_mod_cast hk
      exact (ContDiffOn.continuousLinearMap_comp T h0).continuousOn
    -- two continuous functions on an open set agreeing almost everywhere agree everywhere
    have hdense : ∀ (W : Set ℂ), IsOpen W → ∀ (F₁ F₂ : ℂ → ℂ), ContinuousOn F₁ W →
        ContinuousOn F₂ W → (∀ᵐ z : ℂ, z ∈ W → F₁ z = F₂ z) → ∀ z ∈ W, F₁ z = F₂ z := by
      intro W hW F₁ F₂ hF₁ hF₂ hae z hz
      by_contra hne
      have hEopen : IsOpen {x : ℂ | x ∈ W ∧ F₁ x ≠ F₂ x} := by
        rw [isOpen_iff_mem_nhds]
        intro x hx
        obtain ⟨hxmem, hxne⟩ := hx
        have hdd : ContinuousAt (fun y => F₁ y - F₂ y) x :=
          (hF₁.continuousAt (hW.mem_nhds hxmem)).sub (hF₂.continuousAt (hW.mem_nhds hxmem))
        filter_upwards [hW.mem_nhds hxmem, hdd.eventually_ne (sub_ne_zero.mpr hxne)]
          with y hy1 hy2
        exact ⟨hy1, sub_ne_zero.mp hy2⟩
      have hE0 : MeasureTheory.volume {x : ℂ | x ∈ W ∧ F₁ x ≠ F₂ x} = 0 := by
        refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
        intro x hx
        simp only [Set.mem_ofPred_eq]
        intro hcon
        exact hx.2 (hcon hx.1)
      exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨z, hz, hne⟩).ne' hE0
    have hzeroae : ∀ᵐ z : ℂ, z ≠ 0 := by
      have hset : ({z : ℂ | ¬ (z ≠ 0)} : Set ℂ) = {0} := by ext z; simp
      rw [MeasureTheory.ae_iff, hset]
      simp
    -- `w₀ = f` on `U`
    have hw₀f : ∀ z ∈ U, (fun z => T (fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z)) z = f z := by
      refine hdense U hUopen _ f hw₀cont hfcont.continuousOn ?_
      filter_upwards [hzeroae] with z hz _
      rw [← hDZT (fun y => ((v₀ y : ℝ) : ℂ)) z]
      exact hvpot z hz
    -- transfer of the two Hölder clauses from `w₀` to `f`
    have hIFDf : ∀ (n : ℕ) (w : ℂ), w ∈ U →
        iteratedFDerivWithin ℝ n f U w
          = iteratedFDerivWithin ℝ n (fun z => T (fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z)) U w := by
      intro n w hw
      exact iteratedFDerivWithin_congr (𝕜 := ℝ) (fun x hx => (hw₀f x hx).symm) hw n
    -- the operator-norm comparison of the two iterated derivatives
    have hkey : ∀ x ∈ U, ∀ y ∈ U,
        ‖iteratedFDerivWithin ℝ m f U x - iteratedFDerivWithin ℝ m f U y‖
          ≤ ‖T‖ * ‖iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U x
              - iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U y‖ := by
      intro x hx y hy
      have hcomp : ∀ w ∈ U,
          iteratedFDerivWithin ℝ m
            (fun z => T (fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z)) U w
            = T.compContinuousMultilinearMap
                (iteratedFDerivWithin ℝ m
                  (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U w) := by
        intro w hw
        exact T.iteratedFDerivWithin_comp_left (hfdC.contDiffWithinAt hw) hUunique hw le_rfl
      have hfw : ∀ w ∈ U,
          iteratedFDerivWithin ℝ m (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U w
            = iteratedFDerivWithin ℝ m
                (fderivWithin ℝ (fun z => ((v₀ z : ℝ) : ℂ)) U) U w := by
        intro w hw
        exact iteratedFDerivWithin_congr (𝕜 := ℝ)
          (fun q hq => (fderivWithin_of_isOpen hUopen hq).symm) hw m
      have hEq : ∀ w ∈ U,
          iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U w
            = (continuousMultilinearCurryRightEquiv' ℝ m ℂ ℂ).symm
                (iteratedFDerivWithin ℝ m
                  (fun y => fderivWithin ℝ (fun z => ((v₀ z : ℝ) : ℂ)) U y) U w) := by
        intro w hw
        exact iteratedFDerivWithin_succ_eq_comp_right hUunique hw
      have hnormeq : ‖iteratedFDerivWithin ℝ m
              (fderivWithin ℝ (fun z => ((v₀ z : ℝ) : ℂ)) U) U x
            - iteratedFDerivWithin ℝ m
                (fderivWithin ℝ (fun z => ((v₀ z : ℝ) : ℂ)) U) U y‖
          = ‖iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U x
            - iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U y‖ := by
        have h1 := hEq x hx
        have h2 := hEq y hy
        rw [h1, h2, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      have hsub : T.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U x)
          - T.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U y)
          = T.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U x
              - iteratedFDerivWithin ℝ m
                  (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U y) := by
        ext w
        simp
      rw [hIFDf m x hx, hIFDf m y hy, hcomp x hx, hcomp y hy, hsub]
      refine le_trans (T.norm_compContinuousMultilinearMap_le _) ?_
      rw [hfw x hx, hfw y hy, hnormeq]
    -- the index shift, in the two cases of the Hölder class
    refine hnoH ?_
    rcases hH' with ⟨hα1', hC⟩ | ⟨hαlt, hC, hlo⟩
    · refine Or.inl ⟨hα1', ?_⟩
      have hfdk : ContDiffOn ℝ (((m + 1) : ℕ) : WithTop ℕ∞)
          (fderiv ℝ (fun z => ((v₀ z : ℝ) : ℂ))) U := by
        refine hC.fderiv_of_isOpen hUopen ?_
        rw [show ((1 : WithTop ℕ∞)) = ((1 : ℕ) : WithTop ℕ∞) by norm_num, ← Nat.cast_add]
      have hfk : ContDiffOn ℝ (((m + 1) : ℕ) : WithTop ℕ∞) f U :=
        (ContDiffOn.continuousLinearMap_comp T hfdk).congr (fun z hz => (hw₀f z hz).symm)
      rw [hcast]
      exact hfk
    · refine Or.inr ⟨hαlt, ?_, ?_⟩
      · exact (ContDiffOn.continuousLinearMap_comp T hfdC).congr
          (fun z hz => (hw₀f z hz).symm)
      · intro K hKU hK δ hδ
        obtain ⟨C, hCdef⟩ : ∃ y : ℝ, y = max ‖T‖ 1 := ⟨_, rfl⟩
        have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_right _ _
        have hCpos : (0 : ℝ) < C := by linarith
        have hTC : ‖T‖ ≤ C := by rw [hCdef]; exact le_max_left _ _
        obtain ⟨ρ, hρ, hb⟩ := hlo K hKU hK (δ / C) (by positivity)
        refine ⟨ρ, hρ, ?_⟩
        intro x hx y hy hxy
        have h1 := hkey x (hKU hx) y (hKU hy)
        have h2 := hb x hx y hy hxy
        have h3 : ‖T‖ * ‖iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U x
              - iteratedFDerivWithin ℝ (m + 1) (fun z => ((v₀ z : ℝ) : ℂ)) U y‖
            ≤ C * (δ / C * ‖x - y‖ ^ α) :=
          mul_le_mul hTC h2 (norm_nonneg _) hCpos.le
        have h4 : C * (δ / C * ‖x - y‖ ^ α) = δ * ‖x - y‖ ^ α := by
          field_simp
        linarith [le_trans h1 h3]
  · -- ## Step 7: (d)
    intro H
    have h2α : (0 : ℝ) < 2 - α := by linarith
    have hq1 : (1 : ℝ) ≤ 2 / (2 - α) := by
      rw [le_div_iff₀ h2α]
      linarith
    have hqE : (1 : ENNReal) ≤ ENNReal.ofReal (2 / (2 - α)) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal hq1
    -- continuity gives local `Lˢ` membership on any set
    have hcontLpOn : ∀ (S : ENNReal) (W : Set ℂ) (u : ℂ → ℂ), ContinuousOn u W →
        MemLpLocOn S W u := by
      intro S W u hu K hKW hK
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.mono hKW)
      have hmeas : MeasureTheory.AEStronglyMeasurable (K.indicator u) MeasureTheory.volume := by
        rw [aestronglyMeasurable_indicator_iff hK.measurableSet]
        exact (hu.mono hKW).aestronglyMeasurable hK.measurableSet
      refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top
        (MeasureTheory.memLp_top_of_bound hmeas (max C 0) ?_) ?_ hK.measure_lt_top.ne le_top
      · filter_upwards with z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
          exact le_trans (hC z hz) (le_max_left _ _)
        · rw [Set.indicator_of_notMem hz, norm_zero]
          exact le_max_right _ _
      · intro x hx
        exact Set.indicator_of_notMem hx _
    -- a local `L^q` function against a bounded factor supported in a compact subset
    have hintegr : ∀ (W K : Set ℂ) (u ψ : ℂ → ℂ), K ⊆ W → IsCompact K →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u → Continuous ψ →
        (∀ z : ℂ, z ∉ K → ψ z = 0) →
        MeasureTheory.Integrable (fun z => u z * ψ z) MeasureTheory.volume := by
      intro W K u ψ hKW hK hu hψ hψ0
      have h1 : MeasureTheory.Integrable (K.indicator u) MeasureTheory.volume := by
        refine MeasureTheory.memLp_one_iff_integrable.mp ?_
        exact MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top (hu K hKW hK)
          (fun x hx => Set.indicator_of_notMem hx _) hK.measure_lt_top.ne hqE
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
      have h2 : MeasureTheory.Integrable (fun z => (K.indicator u) z * ψ z)
          MeasureTheory.volume := by
        refine h1.mul_bdd hψ.aestronglyMeasurable (c := max C 0) ?_
        filter_upwards with z
        by_cases hz : z ∈ K
        · exact le_trans (hC z hz) (le_max_left _ _)
        · rw [hψ0 z hz, norm_zero]
          exact le_max_right _ _
      refine h2.congr (Filter.Eventually.of_forall ?_)
      intro z
      simp only
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hψ0 z hz]
        ring
    -- the weak-partial identity is linear in the pair of functions
    have hlinWP : ∀ (W : Set ℂ) (j : Fin 2) (u₁ u₂ w₁ w₂ : ℂ → ℂ) (c₁ c₂ : ℂ),
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₁ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₂ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W w₁ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W w₂ →
        IsWeakPartialOn W j u₁ w₁ → IsWeakPartialOn W j u₂ w₂ →
        IsWeakPartialOn W j (fun z => c₁ * u₁ z + c₂ * u₂ z)
          (fun z => c₁ * w₁ z + c₂ * w₂ z) := by
      intro W j u₁ u₂ w₁ w₂ c₁ c₂ hu₁ hu₂ hw₁ hw₂ h₁ h₂ φ hφ
      have hKsub : tsupport φ ⊆ W := hφ.2.2
      have hKc : IsCompact (tsupport φ) := hφ.2.1
      have hdcont : Continuous (fun z => fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I)) :=
        (ContinuousLinearMap.apply ℝ ℂ (if j = 0 then (1 : ℂ) else Complex.I)).continuous.comp
          (hφ.1.continuous_fderiv (by norm_num))
      have hd0 : ∀ z : ℂ, z ∉ tsupport φ →
          fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I) = 0 := by
        intro z hz
        rw [fderiv_of_notMem_tsupport ℝ hz]
        simp
      have hφ0 : ∀ z : ℂ, z ∉ tsupport φ → φ z = 0 := fun z hz =>
        image_eq_zero_of_notMem_tsupport hz
      have hi1 := hintegr W (tsupport φ) u₁ _ hKsub hKc hu₁ hdcont hd0
      have hi2 := hintegr W (tsupport φ) u₂ _ hKsub hKc hu₂ hdcont hd0
      have hj1 := hintegr W (tsupport φ) w₁ φ hKsub hKc hw₁ hφ.1.continuous hφ0
      have hj2 := hintegr W (tsupport φ) w₂ φ hKsub hKc hw₂ hφ.1.continuous hφ0
      have e1 := h₁ φ hφ
      have e2 := h₂ φ hφ
      show ∫ z : ℂ, (c₁ * u₁ z + c₂ * u₂ z) * fderiv ℝ φ z
          (if j = 0 then (1 : ℂ) else Complex.I)
        = -∫ z : ℂ, (c₁ * w₁ z + c₂ * w₂ z) * φ z
      have hsplit1 : ∫ z : ℂ, (c₁ * u₁ z + c₂ * u₂ z) * fderiv ℝ φ z
            (if j = 0 then (1 : ℂ) else Complex.I)
          = c₁ * (∫ z : ℂ, u₁ z * fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I))
            + c₂ * (∫ z : ℂ, u₂ z * fderiv ℝ φ z (if j = 0 then (1 : ℂ) else Complex.I)) := by
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_add (hi1.const_mul c₁) (hi2.const_mul c₂)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro z
        ring
      have hsplit2 : ∫ z : ℂ, (c₁ * w₁ z + c₂ * w₂ z) * φ z
          = c₁ * (∫ z : ℂ, w₁ z * φ z) + c₂ * (∫ z : ℂ, w₂ z * φ z) := by
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_add (hj1.const_mul c₁) (hj2.const_mul c₂)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro z
        ring
      rw [hsplit1, hsplit2, e1, e2]
      ring
    -- the weak-partial identity is insensitive to an a.e. change of the function
    have hWPae : ∀ (W : Set ℂ) (j : Fin 2) (u u' w : ℂ → ℂ),
        (∀ᵐ z : ℂ, z ∈ W → u z = u' z) → IsWeakPartialOn W j u w →
        IsWeakPartialOn W j u' w := by
      intro W j u u' w hae hwp φ hφ
      have h := hwp φ hφ
      refine Eq.trans ?_ h
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae] with z hz
      by_cases hzW : z ∈ W
      · rw [hz hzW]
      · have hz0 : fderiv ℝ φ z = 0 := by
          refine fderiv_of_notMem_tsupport ℝ ?_
          intro hc
          exact hzW (hφ.2.2 hc)
        rw [hz0]
        simp
    -- local `L^q` membership is closed under linear combinations
    have hLpcomb : ∀ (W : Set ℂ) (u₁ u₂ : ℂ → ℂ) (c₁ c₂ : ℂ),
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₁ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₂ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W
          (fun z => (1 / 2 : ℂ) * (u₁ z - Complex.I * u₂ z)) := by
      intro W u₁ u₂ c₁ c₂ h₁ h₂ K hKW hK
      have e : K.indicator (fun z => (1 / 2 : ℂ) * (u₁ z - Complex.I * u₂ z))
          = fun z => (1 / 2 : ℂ) * (K.indicator u₁ z)
            + (-(Complex.I / 2)) * (K.indicator u₂ z) := by
        funext z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          ring
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
            Set.indicator_of_notMem hz]
          ring
      rw [e]
      exact ((h₁ K hKW hK).const_mul _).add ((h₂ K hKW hK).const_mul _)
    -- the Wirtinger combination of two weak partials
    have hWPform : ∀ (W : Set ℂ) (j : Fin 2) (u₁ u₂ w₁ w₂ : ℂ → ℂ),
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₁ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W u₂ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W w₁ →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) W w₂ →
        IsWeakPartialOn W j u₁ w₁ → IsWeakPartialOn W j u₂ w₂ →
        IsWeakPartialOn W j (fun z => (1 / 2 : ℂ) * (u₁ z - Complex.I * u₂ z))
          (fun z => (1 / 2 : ℂ) * (w₁ z - Complex.I * w₂ z)) := by
      intro W j u₁ u₂ w₁ w₂ hu₁ hu₂ hw₁ hw₂ h₁ h₂
      have hlin := hlinWP W j u₁ u₂ w₁ w₂ (1 / 2 : ℂ) (-(Complex.I / 2))
        hu₁ hu₂ hw₁ hw₂ h₁ h₂
      have e1 : (fun z => (1 / 2 : ℂ) * u₁ z + (-(Complex.I / 2)) * u₂ z)
          = (fun z => (1 / 2 : ℂ) * (u₁ z - Complex.I * u₂ z)) := by
        funext z
        ring
      have e2 : (fun z => (1 / 2 : ℂ) * w₁ z + (-(Complex.I / 2)) * w₂ z)
          = (fun z => (1 / 2 : ℂ) * (w₁ z - Complex.I * w₂ z)) := by
        funext z
        ring
      rw [e1, e2] at hlin
      exact hlin
    -- the translated Sobolev family on `U`
    obtain ⟨D, hD0, hDloc, hDweak⟩ := H
    obtain ⟨D', hD'def⟩ : ∃ F : List (Fin 2) → (ℂ → ℂ),
        F = fun w => (fun z => D w (z - (-z₀))) := ⟨_, rfl⟩
    have hrelU : ∀ z : ℂ, z ∈ U → z - (-z₀) ∈ Ω := by
      intro z hz
      have h := (hUmem z).mp hz
      simpa using h
    have hD'loc : ∀ w : List (Fin 2), w.length ≤ m + 1 + 2 →
        MemLpLocOn (ENNReal.ofReal (2 / (2 - α))) U (D' w) := by
      intro w hw
      rw [hD'def]
      exact hLp (-z₀) Ω U _ (D w) hrelU (hDloc w hw)
    have hD'weak : ∀ (w : List (Fin 2)) (j : Fin 2), w.length < m + 1 + 2 →
        IsWeakPartialOn U j (D' w) (D' (w ++ [j])) := by
      intro w j hw
      rw [hD'def]
      exact hWP (-z₀) Ω U j (D w) (D (w ++ [j])) hrelU (hDweak w j hw)
    have hD'0 : D' [] = fun z => ((v₀ z : ℝ) : ℂ) := by
      funext z
      have h1 : D' [] z = D [] (z - -z₀) := by rw [hD'def]
      rw [h1, hD0]
      simp only
      congr 2
      ring
    -- (7a): the first-order combination agrees with `f` almost everywhere on `U`
    have hzeroae : ∀ᵐ z : ℂ, z ≠ 0 := by
      have hset : ({z : ℂ | ¬ (z ≠ 0)} : Set ℂ) = {0} := by ext z; simp
      rw [MeasureTheory.ae_iff, hset]
      simp
    have hU'open : IsOpen (U \ {(0 : ℂ)}) := hUopen.sdiff isClosed_singleton
    have hU'sub : (U \ {(0 : ℂ)}) ⊆ U := Set.sdiff_subset
    have h7a : ∀ᵐ z : ℂ, z ∈ U →
        (1 / 2 : ℂ) * (D' [0] z - Complex.I * D' [1] z) = f z := by
      have hD'1 : ∀ j : Fin 2, MemLpLocOn 1 (U \ {(0 : ℂ)}) (D' [j]) := by
        intro j K hKU' hK
        refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top
          (hD'loc [j] (by simp only [List.length_cons, List.length_nil]; omega) K
            (hKU'.trans hU'sub) hK)
          (fun x hx => Set.indicator_of_notMem hx _) hK.measure_lt_top.ne hqE
      have hD'w1 : ∀ j : Fin 2,
          IsWeakPartialOn (U \ {(0 : ℂ)}) j (fun z => ((v₀ z : ℝ) : ℂ)) (D' [j]) := by
        intro j φ hφ
        have hφU : IsTestFn U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hU'sub⟩
        have h := hD'weak [] j (by simp only [List.length_nil]; omega) φ hφU
        rw [hD'0] at h
        simpa using h
      have hdiffae : ∀ᵐ z : ℂ, z ∈ (U \ {(0 : ℂ)}) →
          DifferentiableAt ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z := by
        refine Filter.Eventually.of_forall ?_
        intro z hz
        exact ((hv₀sm.differentiableOn (by norm_num)).differentiableAt
          (isOpen_compl_singleton.mem_nhds (by simpa using hz.2)))
      have hbr := WeakPartialEqFDerivAE (U \ {(0 : ℂ)}) hU'open (fun z => ((v₀ z : ℝ) : ℂ))
        (fun j => D' [j])
        (hcontLpOn 1 _ _ ((Complex.continuous_ofReal.comp hv₀cont).continuousOn))
        hD'1 hD'w1 hdiffae
      filter_upwards [hbr 0, hbr 1, hzeroae] with z h0 h1 hz hzU
      have hzU' : z ∈ (U \ {(0 : ℂ)}) := ⟨hzU, by simpa using hz⟩
      have e0 : D' [0] z = fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z 1 := h0 hzU'
      have e1 : D' [1] z = fderiv ℝ (fun y => ((v₀ y : ℝ) : ℂ)) z Complex.I := h1 hzU'
      rw [e0, e1, ← hvpot z hz]
      unfold DZ
      ring
    -- the family for `f` on `U` at the order `m + 2`
    obtain ⟨E, hEdef⟩ : ∃ F : List (Fin 2) → (ℂ → ℂ),
        F = fun w => if w = [] then f else
          (fun z => (1 / 2 : ℂ) * (D' (0 :: w) z - Complex.I * D' (1 :: w) z)) := ⟨_, rfl⟩
    have hE0 : E [] = f := by
      rw [hEdef]
      simp
    have hEne : ∀ w : List (Fin 2), w ≠ [] → E w
        = fun z => (1 / 2 : ℂ) * (D' (0 :: w) z - Complex.I * D' (1 :: w) z) := by
      intro w hw
      rw [hEdef]
      simp only [if_neg hw]
    refine hnoW ⟨E, hE0, ?_, ?_⟩
    · intro w hw
      rcases eq_or_ne w [] with rfl | hwne
      · rw [hE0]
        exact hcontLpOn _ U f hfcont.continuousOn
      · rw [hEne w hwne]
        refine hLpcomb U (D' (0 :: w)) (D' (1 :: w)) (1 / 2 : ℂ) (-(Complex.I / 2)) ?_ ?_
        · exact hD'loc (0 :: w) (by simp only [List.length_cons] at hw ⊢; omega)
        · exact hD'loc (1 :: w) (by simp only [List.length_cons] at hw ⊢; omega)
    · intro w j hw
      have hlen0 : (0 :: w).length < m + 1 + 2 := by
        simp only [List.length_cons] at hw ⊢
        omega
      have hlen1 : (1 :: w).length < m + 1 + 2 := by
        simp only [List.length_cons] at hw ⊢
        omega
      have hform := hWPform U j (D' (0 :: w)) (D' (1 :: w)) (D' (0 :: w ++ [j]))
        (D' (1 :: w ++ [j]))
        (hD'loc (0 :: w) (le_of_lt hlen0)) (hD'loc (1 :: w) (le_of_lt hlen1))
        (hD'loc (0 :: w ++ [j]) (by simp only [List.length_append, List.length_cons,
          List.length_nil] at hw ⊢; omega))
        (hD'loc (1 :: w ++ [j]) (by simp only [List.length_append, List.length_cons,
          List.length_nil] at hw ⊢; omega))
        (by have h := hD'weak (0 :: w) j hlen0; simpa using h)
        (by have h := hD'weak (1 :: w) j hlen1; simpa using h)
      have hwj : (w ++ [j]) ≠ [] := by simp
      rcases eq_or_ne w [] with rfl | hwne
      · rw [hE0, hEne _ hwj]
        refine hWPae U j (fun z => (1 / 2 : ℂ) * (D' [0] z - Complex.I * D' [1] z)) f _ ?_ ?_
        · filter_upwards [h7a] with z hz hzU
          exact hz hzU
        · simpa using hform
      · rw [hEne w hwne, hEne _ hwj]
        simpa using hform
