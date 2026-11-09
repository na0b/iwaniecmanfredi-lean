import IwaniecManfredi.ExtremalInjective
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import IwaniecManfredi.ExtremalHomogeneous
import IwaniecManfredi.Thm2TermSolvesEq18
import IwaniecManfredi.InverseSolvesEq12
import IwaniecManfredi.Eq12ImpliesPHarmonic
import IwaniecManfredi.DExpEqGammaOneInv
import IwaniecManfredi.WirtingerConjRule
import IwaniecManfredi.WeakPartialAcrossPoint
import IwaniecManfredi.WeakPartialEqFDerivAE
import IwaniecManfredi.MemWLocOn

/-- The function `f` of (55) and the `p`-harmonic function `v` of
`paper.tex:592`: the inverse of the extremal map (54) is the complex gradient
of a `p`-harmonic function on the whole plane, and it is smooth off the origin
and homogeneous of degree `d`.  This is the half of Section 7 that the paper's
note lists as a fact to be proved (`paper.tex:113`).

Every regularity statement here is a conclusion, never a hypothesis: the
paper's arrow runs from the equation to the regularity.  `ExtremalH p` is the
`k = 2` summand of the series (19) at `n = 1`, so `Thm2TermSolvesEq18` gives
both its smoothness off the origin and (18); the scaling identity of
`ExtremalPolarForm` spreads (18) from the punctured unit disc to the punctured
plane; the explicit first derivatives of (54) are bounded below off the origin,
so the differential of `ExtremalH p` is invertible there and the inverse is
smooth off the origin with non-vanishing Jacobian; `InverseSolvesEq12` then
gives (12); and the potential is the Euler expression
`v = 2 Re(z f(z))/(d+1)`, whose complex gradient is `f` exactly because (12)
forces `f_z̄` to be real. -/
theorem ExtremalInverseGradient (p : ℝ) (hp : 1 < p) :
    ∃ (f : ℂ → ℂ) (v : ℂ → ℝ),
      Continuous f ∧
      (∀ ξ : ℂ, f (ExtremalH p ξ) = ξ) ∧
      (∀ z : ℂ, ExtremalH p (f z) = z) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : ℂ)}ᶜ) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
        f ((t : ℂ) * z) = ((t ^ DExp p : ℝ) : ℂ) * f z) ∧
      (∀ (w : List (Fin 2)) (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
        PartialWord w f ((t : ℂ) * z)
          = ((t ^ (DExp p - (w.length : ℝ)) : ℝ) : ℂ) * PartialWord w f z) ∧
      Continuous v ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((v z : ℝ) : ℂ)) ({(0 : ℂ)}ᶜ) ∧
      PHarmonicOn p Set.univ v ∧
      (∀ z : ℂ, z ≠ 0 → DZ (fun w => ((v w : ℝ) : ℂ)) z = f z) := by
  -- ## Step 1: `d > 0` and `λ₂ = 1/d`
  have hd : 0 < DExp p := by
    unfold DExp
    have h1 : 0 < 1 / (p - 1) := by positivity
    have h2 : 0 ≤ Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2) := Real.sqrt_nonneg _
    linarith
  obtain ⟨hg0, hgd⟩ := DExpEqGammaOneInv p hp
  have hlam : LambdaCoef 1 2 p = 1 / DExp p := by
    have hge : GammaExp 1 p = LambdaCoef 1 2 p := rfl
    rw [← hge]
    field_simp
    linear_combination hgd
  -- ## Step 2: the inverse `f`, and its only zero
  obtain ⟨hHcont, hHbij, f, hfcont, hfH, hHf⟩ := ExtremalInjective p hp
  have hH0 : ExtremalH p 0 = 0 := by unfold ExtremalH; simp
  have hf0 : f 0 = 0 := by
    have h := hfH 0
    rwa [hH0] at h
  have hfzero : ∀ z : ℂ, f z = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro h
      rw [← hHf z, h, hH0]
    · intro h; rw [h, hf0]
  -- ## Step 3: `ExtremalH p` IS the `k = 2`, `n = 1` summand of (19)
  obtain ⟨A, hAdef⟩ : ∃ a : ℤ → ℂ, a = fun j => if j = 2 then (1 : ℂ) else 0 := ⟨_, rfl⟩
  have hA2 : A ((2 : ℕ) : ℤ) = 1 := by rw [hAdef]; norm_num
  have hident : ∀ ξ : ℂ, ExtremalH p ξ = Thm2Term 1 p A 2 ξ := by
    intro ξ
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      rw [hH0, Thm2Term]
      simp
    · have hN : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hNc : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by simpa using hN.ne'
      have hconj : starRingEnd ℂ ξ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) / ξ := by
        rw [eq_div_iff hξ, mul_comm]
        rw [Complex.mul_conj]
        norm_cast
        rw [Complex.sq_norm]
      have hexp : LambdaCoef 1 2 p + ((1 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) = 1 / DExp p - 1 := by
        rw [hlam]; push_cast; ring
      have hNL : ((‖ξ‖ ^ (1 / DExp p) : ℝ) : ℂ)
          = ((‖ξ‖ ^ (1 / DExp p - 1) : ℝ) : ℂ) * ((‖ξ‖ : ℝ) : ℂ) := by
        have h1 := Real.rpow_add hN (1 / DExp p - 1) 1
        rw [Real.rpow_one, show 1 / DExp p - 1 + 1 = 1 / DExp p by ring] at h1
        rw [h1]
        push_cast
        ring
      rw [ExtremalH, Thm2Term, hA2, map_one, hexp, hNL, hconj, zpow_neg]
      push_cast
      field_simp
  have hThm2 := Thm2TermSolvesEq18 1 p le_rfl hp 2 (by norm_num) A
  have hHsmAt : ∀ ξ : ℂ, ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (ExtremalH p) ξ := by
    intro ξ hξ
    have h := hThm2.1 ξ hξ
    have heq : ExtremalH p = Thm2Term 1 p A 2 := funext hident
    rw [heq]
    exact h
  have hHsm : ContDiffOn ℝ (⊤ : ℕ∞) (ExtremalH p) ({(0 : ℂ)}ᶜ) := by
    intro ξ hξ
    exact (hHsmAt ξ (by simpa using hξ)).contDiffWithinAt
  have hH18disc : SolvesEq18 1 p {ξ : ℂ | ‖ξ‖ < 1} (ExtremalH p) := by
    have heq : ExtremalH p = Thm2Term 1 p A 2 := funext hident
    rw [heq]
    exact hThm2.2.2
  -- two general facts used repeatedly below.  First: two continuous functions on an
  -- open set that agree almost everywhere agree everywhere.
  have hdense : ∀ (W : Set ℂ), IsOpen W → ∀ (F G : ℂ → ℂ), ContinuousOn F W → ContinuousOn G W →
      (∀ᵐ z : ℂ, z ∈ W → F z = G z) → ∀ z ∈ W, F z = G z := by
    intro W hW F G hF hG hae z hz
    by_contra hne
    have hEopen : IsOpen {x : ℂ | x ∈ W ∧ F x ≠ G x} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨hxmem, hxne⟩ := hx
      have hdd : ContinuousAt (fun y => F y - G y) x :=
        (hF.continuousAt (hW.mem_nhds hxmem)).sub (hG.continuousAt (hW.mem_nhds hxmem))
      filter_upwards [hW.mem_nhds hxmem, hdd.eventually_ne (sub_ne_zero.mpr hxne)]
        with y hy1 hy2
      exact ⟨hy1, sub_ne_zero.mp hy2⟩
    have hE0 : MeasureTheory.volume {x : ℂ | x ∈ W ∧ F x ≠ G x} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hcon
      exact hx.2 (hcon hx.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨z, hz, hne⟩).ne' hE0
  -- Second: a function homogeneous of degree `m` has a differential homogeneous of
  -- degree `m - 1`, which is the content of (4) and of Step 15's bound.
  have hdilate : ∀ (F : ℂ → ℂ) (m : ℝ),
      (∀ t : ℝ, 0 < t → ∀ z : ℂ, F ((t : ℂ) * z) = ((t ^ m : ℝ) : ℂ) * F z) →
      (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ F z) →
      ∀ (e : ℂ) (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
        fderiv ℝ F ((t : ℂ) * z) e = ((t ^ (m - 1) : ℝ) : ℂ) * fderiv ℝ F z e := by
    intro F m hhom hFd e t ht z hz
    have htc : ((t : ℂ)) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ht.ne'
    have htz : ((t : ℂ) * z) ≠ 0 := mul_ne_zero htc hz
    have hFA : HasFDerivAt F (fderiv ℝ F ((t : ℂ) * z)) ((t : ℂ) * z) :=
      (hFd _ htz).hasFDerivAt
    have hinner : HasFDerivAt (fun y : ℂ => (t : ℂ) * y)
        ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ)) z := (hasFDerivAt_id z).const_mul (t : ℂ)
    have hA : HasFDerivAt (fun y : ℂ => F ((t : ℂ) * y))
        ((fderiv ℝ F ((t : ℂ) * z)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) z :=
      hFA.comp z hinner
    have hfun : (fun y : ℂ => F ((t : ℂ) * y)) = fun y : ℂ => ((t ^ m : ℝ) : ℂ) * F y :=
      funext (fun y => hhom t ht y)
    rw [hfun] at hA
    have hB : HasFDerivAt (fun y : ℂ => ((t ^ m : ℝ) : ℂ) * F y)
        (((t ^ m : ℝ) : ℂ) • fderiv ℝ F z) z := ((hFd z hz).hasFDerivAt).const_mul _
    have huniq := hA.unique hB
    have happ := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) huniq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at happ
    have hsm : fderiv ℝ F ((t : ℂ) * z) ((t : ℂ) * e)
        = ((t : ℝ) : ℂ) * fderiv ℝ F ((t : ℂ) * z) e := by
      rw [show ((t : ℂ) * e) = (t : ℝ) • e by simp [Complex.real_smul], map_smul,
        Complex.real_smul]
    rw [hsm] at happ
    have htk : (t : ℝ) ^ m = t * t ^ (m - 1) := by
      have h1 := Real.rpow_add ht 1 (m - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (m - 1) = m by ring] at h1
      exact h1
    rw [htk] at happ
    push_cast at happ
    have := mul_left_cancel₀ htc (by linear_combination happ :
      ((t : ℂ)) * fderiv ℝ F ((t : ℂ) * z) e
        = ((t : ℂ)) * (((t ^ (m - 1) : ℝ) : ℂ) * fderiv ℝ F z e))
    exact this
  have hcontLp : ∀ (s : ENNReal) (u : ℂ → ℂ), Continuous u → MemLpLocOn s Set.univ u := by
    intro s u hu K hKsub hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
    have hm : MeasureTheory.AEStronglyMeasurable (K.indicator u) MeasureTheory.volume :=
      (hu.aestronglyMeasurable).indicator hK.measurableSet
    refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top
      (MeasureTheory.memLp_top_of_bound hm (max C 0) ?_) ?_ hK.measure_lt_top.ne le_top
    · filter_upwards with z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        exact le_trans (hC z hz) (le_max_left _ _)
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact le_max_right _ _
    · intro x hx
      exact Set.indicator_of_notMem hx _
  have hsetdiff : (Set.univ : Set ℂ) \ {0} = ({(0 : ℂ)}ᶜ : Set ℂ) := by ext z; simp
  -- Third: a function `C^∞` off the origin whose differential is homogeneous of degree
  -- `m - 1 > -1` has locally integrable first derivatives on all of `ℂ`.  This is (5') and
  -- Step 15's bound; the exponent condition `1 - m < 2` is exactly `m > -1`.
  have hradLp : ∀ (F : ℂ → ℂ) (m : ℝ), 0 < m →
      (∀ ζ : ℂ, ζ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) F ζ) →
      (∀ (e : ℂ) (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
        fderiv ℝ F ((t : ℂ) * z) e = ((t ^ (m - 1) : ℝ) : ℂ) * fderiv ℝ F z e) →
      ∀ e : ℂ, MemLpLocOn 1 Set.univ (fun z : ℂ => fderiv ℝ F z e) := by
    intro F m hm hFsmAt hder e
    have hFsm : ContDiffOn ℝ (⊤ : ℕ∞) F ({(0 : ℂ)}ᶜ) := fun ζ hζ =>
      (hFsmAt ζ (by simpa using hζ)).contDiffWithinAt
    have hFfdc : ContinuousOn (fderiv ℝ F) ({(0 : ℂ)}ᶜ) :=
      hFsm.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
    have hevF : ∀ u : ℂ, ContinuousOn (fun z => fderiv ℝ F z u) ({(0 : ℂ)}ᶜ) := fun u =>
      (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp_continuousOn hFfdc
    have hsubsph : Metric.sphere (0 : ℂ) 1 ⊆ ({(0 : ℂ)}ᶜ : Set ℂ) := by
      intro x hx
      simp only [Metric.mem_sphere, dist_zero_right] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx0
      rw [hx0] at hx
      norm_num at hx
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
      ((hevF e).mono hsubsph)
    -- the radial bound `|dF(z)[e]| ≤ C |z|^(m-1)`, from the point `z/|z|` of the circle
    have hbound : ∀ z : ℂ, z ≠ 0 → ‖fderiv ℝ F z e‖ ≤ max C 0 * ‖z‖ ^ (m - 1) := by
      intro z hz
      have hnz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      have hnzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact hnz.ne'
      obtain ⟨u, hudef⟩ : ∃ y : ℂ, y = z / ((‖z‖ : ℝ) : ℂ) := ⟨_, rfl⟩
      have hune : u ≠ 0 := by rw [hudef]; exact div_ne_zero hz hnzc
      have husph : u ∈ Metric.sphere (0 : ℂ) 1 := by
        simp only [Metric.mem_sphere, dist_zero_right, hudef, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hnz]
        exact div_self hnz.ne'
      have hzu : ((‖z‖ : ℝ) : ℂ) * u = z := by
        rw [hudef]; field_simp
      have h := hder e ‖z‖ hnz u hune
      rw [hzu] at h
      rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (Real.rpow_nonneg (norm_nonneg z) _), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg z) _)
      exact le_trans (hC u husph) (le_max_left _ _)
    have hmeasF : MeasureTheory.AEStronglyMeasurable (fun z : ℂ => fderiv ℝ F z e)
        MeasureTheory.volume := by
      have hcont : ContinuousOn (fun z : ℂ => fderiv ℝ F z e) ({(0 : ℂ)}ᶜ) := hevF e
      have hr : MeasureTheory.volume.restrict ({(0 : ℂ)}ᶜ) = MeasureTheory.volume := by
        refine MeasureTheory.Measure.restrict_eq_self_of_ae_mem ?_
        rw [MeasureTheory.ae_iff]
        simp
      have h := hcont.aestronglyMeasurable (μ := MeasureTheory.volume)
        (measurableSet_singleton (0 : ℂ)).compl
      rwa [hr] at h
    have haeF : ∀ᵐ x : ℂ, ‖fderiv ℝ F x e‖ ≤ max C 0 * ‖x‖ ^ (-(1 - m)) := by
      have hzero : ∀ᵐ x : ℂ, x ≠ 0 := by
        have hset : ({x : ℂ | ¬ (x ≠ 0)} : Set ℂ) = {0} := by ext x; simp
        rw [MeasureTheory.ae_iff, hset]
        simp
      filter_upwards [hzero] with x hx
      rw [show -(1 - m) = m - 1 by ring]
      exact hbound x hx
    have hlocint : MeasureTheory.LocallyIntegrable (fun z : ℂ => fderiv ℝ F z e)
        MeasureTheory.volume :=
      MeasureTheory.locallyIntegrable_of_norm_le_rpow
        (by rw [Complex.finrank_real_complex]; norm_num)
        (by rw [Complex.finrank_real_complex]; push_cast; linarith) haeF hmeasF
    intro K _ hK
    exact MeasureTheory.memLp_one_iff_integrable.mpr
      ((MeasureTheory.integrable_indicator_iff hK.measurableSet).mpr
        (hlocint.integrableOn_isCompact hK))
  -- the pointwise Wirtinger derivatives of `H` are continuous off the origin
  have hHd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ (ExtremalH p) z := fun z hz =>
    (hHsmAt z hz).differentiableAt (by norm_num)
  have hHfdc : ContinuousOn (fderiv ℝ (ExtremalH p)) ({(0 : ℂ)}ᶜ) :=
    hHsm.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  have hevH : ∀ u : ℂ, ContinuousOn (fun ξ => fderiv ℝ (ExtremalH p) ξ u) ({(0 : ℂ)}ᶜ) :=
    fun u => (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp_continuousOn hHfdc
  have hDZHcont : ContinuousOn (fun ξ => DZ (ExtremalH p) ξ) ({(0 : ℂ)}ᶜ) := by
    unfold DZ
    exact continuousOn_const.mul ((hevH 1).sub (continuousOn_const.mul (hevH Complex.I)))
  have hDZbHcont : ContinuousOn (fun ξ => DZbar (ExtremalH p) ξ) ({(0 : ℂ)}ᶜ) := by
    unfold DZbar
    exact continuousOn_const.mul ((hevH 1).add (continuousOn_const.mul (hevH Complex.I)))
  have hne0 : ∀ ξ : ℂ, ξ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) → ξ ≠ 0 := fun ξ hξ => by simpa using hξ
  have hcjne0 : ∀ ξ : ℂ, ξ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) → starRingEnd ℂ ξ ≠ 0 := fun ξ hξ => by
    simpa using hne0 ξ hξ
  have hRHSc : ContinuousOn (fun ξ : ℂ => ((1 / 2 - 1 / p : ℝ) : ℂ) *
      ((ξ / starRingEnd ℂ ξ) * DZ (ExtremalH p) ξ
        + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ (ExtremalH p) ξ)))
      ({(0 : ℂ)}ᶜ) := by
    have hidc : ContinuousOn (fun ξ : ℂ => ξ) ({(0 : ℂ)}ᶜ) := continuousOn_id
    have hcjidc : ContinuousOn (fun ξ : ℂ => starRingEnd ℂ ξ) ({(0 : ℂ)}ᶜ) :=
      Complex.continuous_conj.continuousOn
    have hconjHc : ContinuousOn (fun ξ : ℂ => starRingEnd ℂ (DZ (ExtremalH p) ξ))
        ({(0 : ℂ)}ᶜ) := Complex.continuous_conj.comp_continuousOn hDZHcont
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact (hidc.div hcjidc hcjne0).mul hDZHcont
    · exact (hcjidc.div hidc hne0).mul hconjHc
  -- ## Steps 4, 5, 5': (18) holds at every `ξ ≠ 0`, and on all of `ℂ` weakly
  obtain ⟨μ, hμdef⟩ : ∃ y : ℝ, y = 1 / DExp p := ⟨_, rfl⟩
  -- (3): `H(λ ξ) = λ^μ H(ξ)` for `λ > 0`
  have hHscale : ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      ExtremalH p ((t : ℂ) * z) = ((t ^ μ : ℝ) : ℂ) * ExtremalH p z := by
    intro t ht z
    have hpf := (ExtremalPolarForm p hp).2 (t ^ μ) (Real.rpow_pos_of_pos ht _) z
    have he : ((t ^ μ) ^ DExp p : ℝ) = t := by
      rw [← Real.rpow_mul ht.le, hμdef, one_div, inv_mul_cancel₀ hd.ne', Real.rpow_one]
    rw [he] at hpf
    exact hpf.symm
  have hfds := hdilate (ExtremalH p) μ hHscale hHd
  have hDZs : ∀ t : ℝ, 0 < t → ∀ z : ℂ, z ≠ 0 →
      DZ (ExtremalH p) ((t : ℂ) * z) = ((t ^ (μ - 1) : ℝ) : ℂ) * DZ (ExtremalH p) z := by
    intro t ht z hz
    unfold DZ
    rw [hfds 1 t ht z hz, hfds Complex.I t ht z hz]
    ring
  have hDZbs : ∀ t : ℝ, 0 < t → ∀ z : ℂ, z ≠ 0 →
      DZbar (ExtremalH p) ((t : ℂ) * z)
        = ((t ^ (μ - 1) : ℝ) : ℂ) * DZbar (ExtremalH p) z := by
    intro t ht z hz
    unfold DZbar
    rw [hfds 1 t ht z hz, hfds Complex.I t ht z hz]
    ring
  -- Step 4: (18) at every point of the punctured unit disc
  have hW1open : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hWopen : IsOpen {ξ : ℂ | ξ ≠ 0 ∧ ‖ξ‖ < 1} := by
    have hWeq : {ξ : ℂ | ξ ≠ 0 ∧ ‖ξ‖ < 1} = ({(0 : ℂ)}ᶜ : Set ℂ) ∩ {ξ : ℂ | ‖ξ‖ < 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [hWeq]
    exact isOpen_compl_singleton.inter hW1open
  have hsubW : {ξ : ℂ | ξ ≠ 0 ∧ ‖ξ‖ < 1} ⊆ ({(0 : ℂ)}ᶜ : Set ℂ) := by
    intro x hx
    simpa using hx.1
  have h18step4 : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      DZbar (ExtremalH p) ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * DZ (ExtremalH p) ξ
          + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ (ExtremalH p) ξ)) := by
    obtain ⟨aH, bH, hWW, h18ae⟩ := hH18disc
    obtain ⟨Hx, Hy, hHL, hHxL, hHyL, hHw0, hHw1, haHdef, hbHdef⟩ := hWW
    have hdiffae : ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → DifferentiableAt ℝ (ExtremalH p) ξ := by
      have hzero : ∀ᵐ ξ : ℂ, ξ ≠ 0 := by
        have hset : ({ξ : ℂ | ¬ (ξ ≠ 0)} : Set ℂ) = {0} := by ext ξ; simp
        rw [MeasureTheory.ae_iff, hset]
        simp
      filter_upwards [hzero] with ξ hξ _
      exact hHd ξ hξ
    have hbridge := WeakPartialEqFDerivAE {ξ : ℂ | ‖ξ‖ < 1} hW1open (ExtremalH p)
      (fun j => if j = 0 then Hx else Hy) hHL
      (fun j => by
        fin_cases j
        · show MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} Hx
          exact hHxL
        · show MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} Hy
          exact hHyL)
      (fun j => by
        fin_cases j
        · show IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} 0 (ExtremalH p) Hx
          exact hHw0
        · show IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} 1 (ExtremalH p) Hy
          exact hHw1)
      hdiffae
    have hae : ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ξ ≠ 0 ∧ ‖ξ‖ < 1} →
        DZbar (ExtremalH p) ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
          ((ξ / starRingEnd ℂ ξ) * DZ (ExtremalH p) ξ
            + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ (ExtremalH p) ξ)) := by
      filter_upwards [h18ae, hbridge 0, hbridge 1] with ξ h1 h2 h3 hξ
      have e2 : Hx ξ = fderiv ℝ (ExtremalH p) ξ 1 := h2 hξ.2
      have e3 : Hy ξ = fderiv ℝ (ExtremalH p) ξ Complex.I := h3 hξ.2
      have eaH : aH ξ = DZ (ExtremalH p) ξ := by rw [haHdef ξ, DZ, e2, e3]
      have ebH : bH ξ = DZbar (ExtremalH p) ξ := by rw [hbHdef ξ, DZbar, e2, e3]
      have h := h1 hξ.2 hξ.1
      rw [eaH, ebH] at h
      simpa using h
    intro ξ hξ0 hξ1
    exact hdense _ hWopen _ _ (hDZbHcont.mono hsubW) (hRHSc.mono hsubW) hae ξ ⟨hξ0, hξ1⟩
  -- Step 5: (18) at every `ξ ≠ 0`, by the scaling (3) and the derivative scaling (4)
  have h18pt : ∀ ξ : ℂ, ξ ≠ 0 →
      DZbar (ExtremalH p) ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * DZ (ExtremalH p) ξ
          + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ (ExtremalH p) ξ)) := by
    intro ξ hξ
    have hn0 : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    obtain ⟨lam, hlamdef⟩ : ∃ y : ℝ, y = 1 / (2 * ‖ξ‖) := ⟨_, rfl⟩
    have hlam : 0 < lam := by rw [hlamdef]; positivity
    have hlamc : ((lam : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hlam.ne'
    have hptne : ((lam : ℂ) * ξ) ≠ 0 := mul_ne_zero hlamc hξ
    have hpt : ‖(lam : ℂ) * ξ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam, hlamdef,
        div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    have h4 := h18step4 ((lam : ℂ) * ξ) hptne hpt
    have hcj : starRingEnd ℂ ((lam : ℂ) * ξ) = (lam : ℂ) * starRingEnd ℂ ξ := by
      rw [map_mul, Complex.conj_ofReal]
    have hcjne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
    have hu1 : ((lam : ℂ) * ξ) / starRingEnd ℂ ((lam : ℂ) * ξ) = ξ / starRingEnd ℂ ξ := by
      rw [hcj, mul_div_mul_left _ _ hlamc]
    have hu2 : starRingEnd ℂ ((lam : ℂ) * ξ) / ((lam : ℂ) * ξ) = starRingEnd ℂ ξ / ξ := by
      rw [hcj, mul_div_mul_left _ _ hlamc]
    rw [hDZs lam hlam ξ hξ, hDZbs lam hlam ξ hξ, hu1, hu2, map_mul,
      Complex.conj_ofReal] at h4
    have hLne : ((lam ^ (μ - 1) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact (Real.rpow_pos_of_pos hlam _).ne'
    refine mul_left_cancel₀ hLne ?_
    linear_combination h4
  have hH18 : SolvesEq18 1 p Set.univ (ExtremalH p) := by
    have hμpos : 0 < μ := by rw [hμdef]; positivity
    have hHloc : MemLpLocOn 1 Set.univ (ExtremalH p) := hcontLp 1 _ hHcont
    -- (5'): the first partials of `H` are locally integrable, by the radial bound
    have hPWloc : ∀ j : Fin 2, MemLpLocOn 1 Set.univ (PartialWord [j] (ExtremalH p)) := by
      intro j
      obtain ⟨e, hedef⟩ : ∃ y : ℂ, y = (if j = 0 then 1 else Complex.I) := ⟨_, rfl⟩
      have hpw : PartialWord [j] (ExtremalH p) = fun z : ℂ => fderiv ℝ (ExtremalH p) z e := by
        funext z
        rw [hedef]
        rfl
      rw [hpw]
      exact hradLp (ExtremalH p) μ hμpos hHsmAt hfds e
    -- the classical partials are the distributional ones, across the origin
    have hweak : ∀ j : Fin 2,
        IsWeakPartialOn Set.univ j (ExtremalH p) (PartialWord [j] (ExtremalH p)) := by
      intro j
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
        hHcont.continuousOn
      refine WeakPartialAcrossPoint Set.univ isOpen_univ {(0 : ℂ)} (Set.subset_univ _)
        (fun Kc _ _ => Set.Finite.subset (Set.finite_singleton 0) Set.inter_subset_left)
        j (ExtremalH p) (PartialWord [j] (ExtremalH p)) 0 le_rfl (by norm_num)
        ?_ (fun z _ => rfl) hHloc (hPWloc j) ?_
      · rw [hsetdiff]
        exact hHsm.of_le (by norm_num)
      · intro z₀ hz₀
        refine ⟨max M 0, 1, by norm_num, ?_⟩
        intro z _ hlt
        have hz0 : z₀ = 0 := by simpa using hz₀
        subst hz0
        have hone : ‖z - (0 : ℂ)‖ ^ (-(0 : ℝ)) = 1 := by
          rw [neg_zero, Real.rpow_zero]
        rw [hone, mul_one]
        have hmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
          simp only [Metric.mem_closedBall, dist_zero_right]
          simpa using hlt.le
        exact le_trans (hM z hmem) (le_max_left _ _)
    refine ⟨DZ (ExtremalH p), DZbar (ExtremalH p),
      ⟨PartialWord [0] (ExtremalH p), PartialWord [1] (ExtremalH p),
        hHloc, hPWloc 0, hPWloc 1, hweak 0, hweak 1, ?_, ?_⟩, ?_⟩
    · intro z
      rfl
    · intro z
      rfl
    · refine Filter.Eventually.of_forall ?_
      intro ξ _ hξ
      simpa using h18pt ξ hξ
  -- ## Steps 6, 7: the differential of `H` is injective off the origin
  have hJacH : ∀ ξ : ℂ, ξ ≠ 0 → Jac (ExtremalH p) ξ ≠ 0 := by
    intro ξ hξ
    have hn : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hnc : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hn.ne'
    obtain ⟨μ, hμdef⟩ : ∃ y : ℝ, y = 1 / DExp p := ⟨_, rfl⟩
    have hμ : 0 < μ := by rw [hμdef]; positivity
    obtain ⟨ε, hεdef⟩ : ∃ y : ℝ, y = EpsCoef 1 2 p := ⟨_, rfl⟩
    have hε : |ε| < 1 / 3 := by rw [hεdef]; exact (ExtremalEpsBound p hp).2.1
    -- ### Step 6: `H_ξ ≠ 0` off the origin, from the two-term form of (54)
    have hbrickA : ∀ ζ : ℂ, ζ ≠ 0 →
        ExtremalH p ζ = ζ * ((‖ζ‖ ^ (μ - 1) : ℝ) : ℂ)
          + ((ε : ℝ) : ℂ) * ((‖ζ‖ ^ (μ + 3) : ℝ) : ℂ) * ζ ^ (-3 : ℤ) := by
      intro ζ hζ
      have hnz : (0 : ℝ) < ‖ζ‖ := norm_pos_iff.mpr hζ
      have hnzc : ((‖ζ‖ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact hnz.ne'
      have hζ3 : ζ ^ 3 ≠ 0 := pow_ne_zero _ hζ
      have e1 : (‖ζ‖ ^ (μ - 1) : ℝ) = ‖ζ‖ ^ μ / ‖ζ‖ := by
        rw [Real.rpow_sub hnz, Real.rpow_one]
      have e2 : (‖ζ‖ ^ (μ + 3) : ℝ) = ‖ζ‖ ^ μ * ‖ζ‖ ^ (3 : ℕ) := by
        rw [Real.rpow_add hnz]
        norm_num [Real.rpow_natCast]
      rw [hεdef, hμdef] at *
      unfold ExtremalH
      rw [e1, e2]
      push_cast
      rw [zpow_neg]
      norm_num
      field_simp
    obtain ⟨hmpsm1, hmpz1, -⟩ := WirtingerModulusPowerRule (μ - 1) ξ hξ
    obtain ⟨hmpsm2, hmpz2, -⟩ := WirtingerModulusPowerRule (μ + 3) ξ hξ
    have hdf1 : DifferentiableAt ℝ (fun z : ℂ => ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)) ξ :=
      hmpsm1.differentiableAt (by norm_num)
    have hdf2 : DifferentiableAt ℝ (fun z : ℂ => ((‖z‖ ^ (μ + 3) : ℝ) : ℂ)) ξ :=
      hmpsm2.differentiableAt (by norm_num)
    have hdz3 : DifferentiableAt ℝ (fun z : ℂ => z ^ (-3 : ℤ)) ξ :=
      ((differentiableAt_zpow (𝕜 := ℂ) (m := (-3 : ℤ)) (x := ξ)).mpr
        (Or.inl hξ)).restrictScalars ℝ
    have hDZid1 : DZ (fun y : ℂ => y) ξ = 1 := by unfold DZ; simp; norm_num
    have hpow := (WirtingerPowerRule (fun y : ℂ => y) ({(0 : ℂ)}ᶜ) isOpen_compl_singleton
        contDiffOn_id (fun ζ hζ => by simpa using hζ) (-3) ξ (by simpa using hξ)).1
    rw [hDZid1, mul_one] at hpow
    obtain ⟨hT1, -⟩ := WirtingerProductRule (fun y : ℂ => y)
      (fun z : ℂ => ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)) ξ differentiable_id.differentiableAt hdf1
    rw [hDZid1, hmpz1] at hT1
    have hcmul : DZ (fun z : ℂ => ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ)) ξ
        = ((ε : ℝ) : ℂ) * DZ (fun z : ℂ => ((‖z‖ ^ (μ + 3) : ℝ) : ℂ)) ξ := by
      unfold DZ
      rw [fderiv_const_mul hdf2]
      simp only [smul_apply, smul_eq_mul]
      ring
    obtain ⟨hT2, -⟩ := WirtingerProductRule
      (fun z : ℂ => ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ))
      (fun z : ℂ => z ^ (-3 : ℤ)) ξ (hdf2.const_mul _) hdz3
    rw [hcmul, hmpz2, hpow] at hT2
    have hDZcongr : ∀ (F G : ℂ → ℂ) (u : ℂ), (∀ᶠ y in nhds u, F y = G y) → DZ F u = DZ G u := by
      intro F G u h
      unfold DZ
      rw [(Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h)]
    have hsumeq : DZ (ExtremalH p) ξ
        = DZ (fun z : ℂ => z * ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)
            + ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ) * z ^ (-3 : ℤ)) ξ := by
      refine hDZcongr _ _ ξ ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds (show ξ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) by
        simpa using hξ)] with y hy
      exact hbrickA y (by simpa using hy)
    have hadd : DZ (fun z : ℂ => z * ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)
          + ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ) * z ^ (-3 : ℤ)) ξ
        = DZ (fun z : ℂ => z * ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)) ξ
          + DZ (fun z : ℂ => ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ) * z ^ (-3 : ℤ)) ξ := by
      have hD : fderiv ℝ (fun z : ℂ => z * ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)
            + ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ) * z ^ (-3 : ℤ)) ξ
          = fderiv ℝ (fun z : ℂ => z * ((‖z‖ ^ (μ - 1) : ℝ) : ℂ)) ξ
            + fderiv ℝ (fun z : ℂ => ((ε : ℝ) : ℂ) * ((‖z‖ ^ (μ + 3) : ℝ) : ℂ) * z ^ (-3 : ℤ)) ξ :=
        fderiv_fun_add (differentiable_id.differentiableAt.mul hdf1)
          ((hdf2.const_mul _).mul hdz3)
      unfold DZ
      rw [hD]
      simp only [add_apply]
      ring
    have hclosed : DZ (ExtremalH p) ξ
        = (((μ + 1) / 2 : ℝ) : ℂ) * ((‖ξ‖ ^ (μ - 1) : ℝ) : ℂ)
          + ((ε * ((μ - 3) / 2) : ℝ) : ℂ) * ((‖ξ‖ ^ (μ + 3) : ℝ) : ℂ) * ξ ^ (-4 : ℤ) := by
      rw [hsumeq, hadd, hT1, hT2]
      have hz4 : ξ ^ (-3 : ℤ) = ξ * ξ ^ (-4 : ℤ) := by
        rw [show (-3 : ℤ) = 1 + (-4 : ℤ) by norm_num, zpow_add₀ hξ, zpow_one]
      rw [hz4]
      push_cast
      field_simp
      ring
    have hposnum : 0 < (μ + 1) - |ε| * |μ - 3| := by
      have h0 : 0 ≤ |μ - 3| := abs_nonneg _
      have h1 : 0 ≤ |ε| := abs_nonneg _
      rcases abs_choice (μ - 3) with h | h <;> rw [h] <;> nlinarith
    obtain ⟨R, hRdef⟩ : ∃ y : ℝ, y = ‖ξ‖ ^ (μ - 1) := ⟨_, rfl⟩
    have hR : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hn _
    have hnormA : ‖(((μ + 1) / 2 : ℝ) : ℂ) * ((‖ξ‖ ^ (μ - 1) : ℝ) : ℂ)‖ = (μ + 1) / 2 * R := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < (μ + 1) / 2),
        abs_of_pos (Real.rpow_pos_of_pos hn _), hRdef]
    have hnormB : ‖((ε * ((μ - 3) / 2) : ℝ) : ℂ) * ((‖ξ‖ ^ (μ + 3) : ℝ) : ℂ) * ξ ^ (-4 : ℤ)‖
        = |ε| * |μ - 3| / 2 * R := by
      have h1 : |ε * ((μ - 3) / 2)| = |ε| * |μ - 3| / 2 := by
        rw [abs_mul, abs_div, abs_two]
        ring
      have h2 : ‖ξ‖ ^ (μ + 3) * ‖ξ‖ ^ (-4 : ℤ) = R := by
        rw [← Real.rpow_intCast ‖ξ‖ (-4), ← Real.rpow_add hn, hRdef]
        congr 1
        push_cast
        ring
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _), norm_zpow, h1, mul_assoc, h2]
    have hHx : DZ (ExtremalH p) ξ ≠ 0 := by
      have hlow : 0 < ‖DZ (ExtremalH p) ξ‖ := by
        rw [hclosed]
        have h1 := norm_sub_norm_le ((((μ + 1) / 2 : ℝ) : ℂ) * ((‖ξ‖ ^ (μ - 1) : ℝ) : ℂ))
          (-(((ε * ((μ - 3) / 2) : ℝ) : ℂ) * ((‖ξ‖ ^ (μ + 3) : ℝ) : ℂ) * ξ ^ (-4 : ℤ)))
        rw [norm_neg, sub_neg_eq_add, hnormA, hnormB] at h1
        nlinarith [h1, hposnum, hR]
      intro hzero
      rw [hzero] at hlow
      norm_num at hlow
    -- ### Step 7: `Jac` is the difference of squares, and (18) bounds `H_ξ̄` by `H_ξ`
    have hp0 : (0 : ℝ) < p := by linarith
    have hcne : ‖((1 / 2 - 1 / p : ℝ) : ℂ)‖ = |1 / 2 - 1 / p| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hu1 : ‖ξ / starRingEnd ℂ ξ‖ = 1 := by
      rw [norm_div, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr hξ)]
    have hu2 : ‖(starRingEnd ℂ ξ) / ξ‖ = 1 := by
      rw [norm_div, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr hξ)]
    have hbd : ‖DZbar (ExtremalH p) ξ‖
        ≤ (2 * |1 / 2 - 1 / p|) * ‖DZ (ExtremalH p) ξ‖ := by
      rw [h18pt ξ hξ, norm_mul, hcne]
      have h := norm_add_le ((ξ / starRingEnd ℂ ξ) * DZ (ExtremalH p) ξ)
        (((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ (ExtremalH p) ξ))
      rw [norm_mul, norm_mul, hu1, hu2, one_mul, one_mul, RCLike.norm_conj] at h
      nlinarith [abs_nonneg (1 / 2 - 1 / p), norm_nonneg (DZ (ExtremalH p) ξ), h]
    have hlt : 2 * |1 / 2 - 1 / p| < 1 := by
      have hid : (2 : ℝ) * |1 / 2 - 1 / p| = |p - 2| / p := by
        rw [show (1 : ℝ) / 2 - 1 / p = (p - 2) / (2 * p) by field_simp,
          abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * p)]
        field_simp
      rw [hid, div_lt_one hp0]
      rcases abs_cases (p - 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
    have hxpos : 0 < ‖DZ (ExtremalH p) ξ‖ := norm_pos_iff.mpr hHx
    have hstrict : ‖DZbar (ExtremalH p) ξ‖ < ‖DZ (ExtremalH p) ξ‖ := by
      nlinarith [hbd, hlt, hxpos, norm_nonneg (DZbar (ExtremalH p) ξ)]
    unfold Jac
    nlinarith [norm_nonneg (DZbar (ExtremalH p) ξ), hxpos, hstrict]
  -- the Wirtinger form of the real differential (needs no differentiability)
  have hwform : ∀ (F : ℂ → ℂ) (u h : ℂ),
      fderiv ℝ F u h = DZ F u * h + DZbar F u * starRingEnd ℂ h := by
    intro F u h
    have hh : h = (h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hh]
    have h1 : fderiv ℝ F u ((h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I)
        = h.re • fderiv ℝ F u 1 + h.im • fderiv ℝ F u Complex.I := by
      rw [show ((h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I)
          = h.re • (1 : ℂ) + h.im • Complex.I by
        simp [Complex.real_smul]]
      rw [map_add, map_smul, map_smul]
    rw [h1, DZ, DZbar]
    simp only [Complex.real_smul]
    have hI : Complex.I * Complex.I = -1 := by simp
    apply Complex.ext <;> simp <;> ring
  have hinjH : ∀ ξ : ℂ, ξ ≠ 0 → Function.Injective (fderiv ℝ (ExtremalH p) ξ) := by
    intro ξ hξ
    have hJ := hJacH ξ hξ
    have hne : ‖DZ (ExtremalH p) ξ‖ ≠ ‖DZbar (ExtremalH p) ξ‖ := by
      intro hc
      apply hJ
      unfold Jac
      rw [hc]
      ring
    -- the kernel is trivial: `a h + b conj h = 0` with `‖a‖ ≠ ‖b‖` forces `h = 0`
    have hker : ∀ h : ℂ, fderiv ℝ (ExtremalH p) ξ h = 0 → h = 0 := by
      intro h hh
      rw [hwform] at hh
      rcases eq_or_ne h 0 with h0 | h0
      · exact h0
      · exfalso
        have hhn : (0 : ℝ) < ‖h‖ := norm_pos_iff.mpr h0
        have hsplit : DZ (ExtremalH p) ξ * h
            = -(DZbar (ExtremalH p) ξ * starRingEnd ℂ h) := by linear_combination hh
        have hnorm : ‖DZ (ExtremalH p) ξ‖ * ‖h‖ = ‖DZbar (ExtremalH p) ξ‖ * ‖h‖ := by
          have h1 : ‖DZ (ExtremalH p) ξ * h‖
              = ‖DZbar (ExtremalH p) ξ * starRingEnd ℂ h‖ := by
            rw [hsplit, norm_neg]
          rw [norm_mul, norm_mul, RCLike.norm_conj] at h1
          exact h1
        exact hne (by
          have := mul_right_cancel₀ (ne_of_gt hhn) hnorm
          exact this)
    intro h1 h2 heq
    have h0 : fderiv ℝ (ExtremalH p) ξ (h1 - h2) = 0 := by
      rw [map_sub, heq, sub_self]
    have := hker _ h0
    linear_combination this
  -- ## Step 8: `f` is `C^∞` off the origin, by the inverse function theorem
  have hfsmAt : ∀ z : ℂ, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) f z := by
    intro z hz
    have hfz : f z ≠ 0 := fun hc => hz ((hfzero z).mp hc)
    have hHa : ExtremalH p (f z) = z := hHf z
    have hHsmA : ContDiffAt ℝ (⊤ : ℕ∞) (ExtremalH p) (f z) := hHsmAt (f z) hfz
    have hinjA : Function.Injective (fderiv ℝ (ExtremalH p) (f z)) := hinjH (f z) hfz
    -- injectivity alone gives the continuous linear equiv, in finite dimensions
    have hsurj : Function.Surjective (fderiv ℝ (ExtremalH p) (f z)) :=
      (LinearMap.injective_iff_surjective
        (f := (fderiv ℝ (ExtremalH p) (f z) : ℂ →ₗ[ℝ] ℂ))).mp hinjA
    let e : ℂ ≃L[ℝ] ℂ :=
      (LinearEquiv.ofBijective (fderiv ℝ (ExtremalH p) (f z) : ℂ →ₗ[ℝ] ℂ)
        ⟨hinjA, hsurj⟩).toContinuousLinearEquiv
    have hfd : HasFDerivAt (ExtremalH p) (e : ℂ →L[ℝ] ℂ) (f z) := by
      have hcoe : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ (ExtremalH p) (f z) := by ext x; rfl
      rw [hcoe]
      exact (hHsmA.differentiableAt (by norm_num)).hasFDerivAt
    have hloc := hHsmA.to_localInverse (f' := e) hfd (by norm_num)
    -- the global inverse `f` agrees with the local one near `z`
    have hgoal : ContDiffAt ℝ (⊤ : ℕ∞) f (ExtremalH p (f z)) := by
      refine hloc.congr_of_eventuallyEq ?_
      have hstrict := hHsmA.hasStrictFDerivAt' hfd (by norm_num)
      have hleft := hstrict.eventually_left_inverse
      have htend : Filter.Tendsto f (nhds (ExtremalH p (f z))) (nhds (f z)) := by
        have h := hfcont.continuousAt (x := ExtremalH p (f z))
        rw [ContinuousAt, hfH (f z)] at h
        exact h
      filter_upwards [htend.eventually hleft] with y hy
      rw [hHf y] at hy
      exact hy.symm
    rwa [hHa] at hgoal
  have hfsm : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : ℂ)}ᶜ) := fun z hz =>
    (hfsmAt z (by simpa using hz)).contDiffWithinAt
  have hfdOff : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℝ f z := by
    intro z hz
    exact (hfsm.differentiableOn (by norm_num)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hz))
  -- ## Step 9: homogeneity, which does not depend on (12)
  obtain ⟨hhom1, hhom2⟩ := ExtremalHomogeneous p hp f hfH hHf hfsm
  -- ## Steps 10, 11, 12: `f` solves (12), and `f_z̄` is real off the origin
  -- the converse half of Step 7, needed for `f` at Step 11: an injective differential
  -- forces `J ≠ 0`.  A kernel vector is a square root of the unit number `-b/a`.
  have hJacOfInj : ∀ (F : ℂ → ℂ) (z : ℂ), Function.Injective (fderiv ℝ F z) →
      Jac F z ≠ 0 := by
    intro F z hinj hJ
    unfold Jac at hJ
    obtain ⟨a, hadef⟩ : ∃ y : ℂ, y = DZ F z := ⟨_, rfl⟩
    obtain ⟨b, hbdef⟩ : ∃ y : ℂ, y = DZbar F z := ⟨_, rfl⟩
    have hnn : ‖a‖ = ‖b‖ := by
      rw [hadef, hbdef]
      nlinarith [norm_nonneg (DZ F z), norm_nonneg (DZbar F z), hJ]
    have hfd : ∀ h : ℂ, fderiv ℝ F z h = a * h + b * starRingEnd ℂ h := by
      intro h
      rw [hadef, hbdef]
      exact hwform F z h
    have hzero0 : fderiv ℝ F z 0 = 0 := by rw [hfd 0]; simp
    rcases eq_or_ne a 0 with ha | ha
    · have hb : b = 0 := by
        have h0 : ‖b‖ = 0 := by rw [← hnn, ha, norm_zero]
        exact norm_eq_zero.mp h0
      have h1 : fderiv ℝ F z 1 = 0 := by rw [hfd 1, ha, hb]; ring
      exact one_ne_zero (hinj (h1.trans hzero0.symm))
    · have hbne : b ≠ 0 := by
        intro hb0
        rw [hb0, norm_zero] at hnn
        exact ha (norm_eq_zero.mp hnn)
      obtain ⟨u, hudef⟩ : ∃ y : ℂ, y = -b / a := ⟨_, rfl⟩
      have hune : u ≠ 0 := by rw [hudef]; exact div_ne_zero (neg_ne_zero.mpr hbne) ha
      have hnu : ‖u‖ = 1 := by
        rw [hudef, norm_div, norm_neg, ← hnn, div_self (norm_ne_zero_iff.mpr ha)]
      obtain ⟨h, hhdef⟩ : ∃ y : ℂ, y = Complex.exp (((u.arg / 2 : ℝ) : ℂ) * Complex.I) :=
        ⟨_, rfl⟩
      have hhne : h ≠ 0 := by rw [hhdef]; exact Complex.exp_ne_zero _
      have hsq : h ^ 2 = u := by
        have h1 : Complex.exp ((u.arg : ℂ) * Complex.I) = u := by
          have h2 := Complex.norm_mul_exp_arg_mul_I u
          rw [hnu] at h2
          simpa using h2
        have h3 : h ^ 2 = Complex.exp ((u.arg : ℂ) * Complex.I) := by
          rw [hhdef, sq, ← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [h3, h1]
      have hconjx : starRingEnd ℂ (((u.arg / 2 : ℝ) : ℂ) * Complex.I)
          = -(((u.arg / 2 : ℝ) : ℂ) * Complex.I) := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      have hprod : h * starRingEnd ℂ h = 1 := by
        rw [hhdef, ← Complex.exp_conj, hconjx, ← Complex.exp_add, add_neg_cancel,
          Complex.exp_zero]
      have hau : a * u = -b := by rw [hudef]; field_simp
      have hzero : h * (a * h + b * starRingEnd ℂ h) = 0 := by
        have he : h * (a * h + b * starRingEnd ℂ h)
            = a * h ^ 2 + b * (h * starRingEnd ℂ h) := by ring
        rw [he, hsq, hprod, hau]
        ring
      have hker : fderiv ℝ F z h = 0 := by
        rw [hfd h]
        rcases mul_eq_zero.mp hzero with h0 | h0
        · exact absurd h0 hhne
        · exact h0
      exact hhne (hinj (hker.trans hzero0.symm))
  -- ## Steps 10, 11: `f ∈ W^{1,1}_loc(ℂ)`, and `f` solves (12) on `ℂ`
  have hf12 : SolvesEq12 p Set.univ f := by
    have himg : ExtremalH p '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ]
      exact fun z => ⟨f z, hHf z⟩
    -- Step 10: the first partials of `f` are locally integrable, by (c) and the radial bound
    have hfdsf := hdilate f (DExp p) (fun t ht z => hhom1 t ht.le z) hfdOff
    have hfloc1 : MemLpLocOn 1 Set.univ f := hcontLp 1 _ hfcont
    have hPWfloc : ∀ j : Fin 2, MemLpLocOn 1 Set.univ (PartialWord [j] f) := by
      intro j
      obtain ⟨e, hedef⟩ : ∃ y : ℂ, y = (if j = 0 then 1 else Complex.I) := ⟨_, rfl⟩
      have hpw : PartialWord [j] f = fun z : ℂ => fderiv ℝ f z e := by
        funext z
        rw [hedef]
        rfl
      rw [hpw]
      exact hradLp f (DExp p) hd hfsmAt hfdsf e
    have hweakf : ∀ j : Fin 2, IsWeakPartialOn Set.univ j f (PartialWord [j] f) := by
      intro j
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
        hfcont.continuousOn
      refine WeakPartialAcrossPoint Set.univ isOpen_univ {(0 : ℂ)} (Set.subset_univ _)
        (fun Kc _ _ => Set.Finite.subset (Set.finite_singleton 0) Set.inter_subset_left)
        j f (PartialWord [j] f) 0 le_rfl (by norm_num)
        ?_ (fun z _ => rfl) hfloc1 (hPWfloc j) ?_
      · rw [hsetdiff]
        exact hfsm.of_le (by norm_num)
      · intro z₀ hz₀
        refine ⟨max M 0, 1, by norm_num, ?_⟩
        intro z _ hlt
        have hz0 : z₀ = 0 := by simpa using hz₀
        subst hz0
        have hone : ‖z - (0 : ℂ)‖ ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
        rw [hone, mul_one]
        have hmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
          simp only [Metric.mem_closedBall, dist_zero_right]
          simpa using hlt.le
        exact le_trans (hM z hmem) (le_max_left _ _)
    have hfW : MemWLocOn 1 1 (ExtremalH p '' Set.univ) f := by
      rw [himg]
      refine ⟨fun w => PartialWord w f, rfl, ?_, ?_⟩
      · intro w hw
        rcases w with _ | ⟨j, w'⟩
        · exact hfloc1
        · rcases w' with _ | ⟨k, w''⟩
          · exact hPWfloc j
          · simp only [List.length_cons] at hw
            exact absurd hw (by omega)
      · intro w j hw
        rcases w with _ | ⟨i, w'⟩
        · exact hweakf j
        · simp only [List.length_cons] at hw
          exact absurd hw (by omega)
    have hzeroae : ∀ᵐ z : ℂ, z ≠ 0 := by
      have hset : ({z : ℂ | ¬ (z ≠ 0)} : Set ℂ) = {0} := by ext z; simp
      rw [MeasureTheory.ae_iff, hset]
      simp
    have hfdiff : ∀ᵐ z : ℂ, z ∈ ExtremalH p '' Set.univ → DifferentiableAt ℝ f z := by
      filter_upwards [hzeroae] with z hz _
      exact hfdOff z hz
    -- Step 8's Jacobian clause: `d f(z)` is injective because `H ∘ f = id`
    have hinjf : ∀ z : ℂ, z ≠ 0 → Function.Injective (fderiv ℝ f z) := by
      intro z hz
      have hfz : f z ≠ 0 := fun hc => hz ((hfzero z).mp hc)
      have hcomp : HasFDerivAt (fun y : ℂ => ExtremalH p (f y))
          ((fderiv ℝ (ExtremalH p) (f z)).comp (fderiv ℝ f z)) z :=
        (hHd (f z) hfz).hasFDerivAt.comp z (hfdOff z hz).hasFDerivAt
      have heqf : (fun y : ℂ => ExtremalH p (f y)) = fun y : ℂ => y := funext hHf
      rw [heqf] at hcomp
      have hid : HasFDerivAt (fun y : ℂ => y) (ContinuousLinearMap.id ℝ ℂ) z :=
        hasFDerivAt_id z
      have hcl := hcomp.unique hid
      intro x y hxy
      have hx : (fderiv ℝ (ExtremalH p) (f z)).comp (fderiv ℝ f z) x
          = (fderiv ℝ (ExtremalH p) (f z)).comp (fderiv ℝ f z) y := by
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
        rw [hxy]
      rw [hcl] at hx
      simpa using hx
    have hfJ : ∀ᵐ z : ℂ, z ∈ ExtremalH p '' Set.univ → Jac f z ≠ 0 := by
      filter_upwards [hzeroae] with z hz _
      exact hJacOfInj f z (hinjf z hz)
    -- Step 11: `InverseSolvesEq12`
    have hres := InverseSolvesEq12 p hp Set.univ isOpen_univ (ExtremalH p) f
      (by rw [himg]; exact isOpen_univ)
      (by rw [hsetdiff]; exact hHsm.of_le (by norm_num))
      hH18 (fun ξ _ => hfH ξ) hfW hfdiff hfJ
    rwa [himg] at hres
  -- ## Step 12: (12) at EVERY `z ≠ 0`, and `f_z̄` real there
  have hfdc : ContinuousOn (fderiv ℝ f) ({(0 : ℂ)}ᶜ) :=
    hfsm.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  have hev : ∀ u : ℂ, ContinuousOn (fun z => fderiv ℝ f z u) ({(0 : ℂ)}ᶜ) := fun u =>
    (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp_continuousOn hfdc
  have hDZcont : ContinuousOn (fun z => DZ f z) ({(0 : ℂ)}ᶜ) := by
    unfold DZ
    exact continuousOn_const.mul ((hev 1).sub (continuousOn_const.mul (hev Complex.I)))
  have hDZbcont : ContinuousOn (fun z => DZbar f z) ({(0 : ℂ)}ᶜ) := by
    unfold DZbar
    exact continuousOn_const.mul ((hev 1).add (continuousOn_const.mul (hev Complex.I)))
  have hfneOff : ∀ z : ℂ, z ∈ ({(0 : ℂ)}ᶜ : Set ℂ) → f z ≠ 0 := by
    intro z hz hc
    exact (by simpa using hz : z ≠ 0) ((hfzero z).mp hc)
  have hfC : ContinuousOn f ({(0 : ℂ)}ᶜ) := hfcont.continuousOn
  have hcjC : ContinuousOn (fun z => starRingEnd ℂ (f z)) ({(0 : ℂ)}ᶜ) :=
    Complex.continuous_conj.comp_continuousOn hfC
  have hcjne : ∀ z : ℂ, z ∈ ({(0 : ℂ)}ᶜ : Set ℂ) → starRingEnd ℂ (f z) ≠ 0 := fun z hz => by
    simpa using hfneOff z hz
  have h12pt : ∀ z : ℂ, z ≠ 0 →
      DZbar f z = ((1 / p - 1 / 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)) := by
    have hRHSc : ContinuousOn (fun z : ℂ => ((1 / p - 1 / 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z))) ({(0 : ℂ)}ᶜ) := by
      refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
      · exact (hcjC.div hfC hfneOff).mul hDZcont
      · exact (hfC.div hcjC hcjne).mul (Complex.continuous_conj.comp_continuousOn hDZcont)
    have hae : ∀ᵐ z : ℂ, z ∈ ({(0 : ℂ)}ᶜ : Set ℂ) →
        DZbar f z = ((1 / p - 1 / 2 : ℝ) : ℂ) *
          ((starRingEnd ℂ (f z) / f z) * DZ f z
            + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)) := by
      obtain ⟨af, bf, hWW, h12ae⟩ := hf12
      obtain ⟨fx, fy, hfL, hfxL, hfyL, hfw0, hfw1, hafdef, hbfdef⟩ := hWW
      have hfdae : ∀ᵐ z : ℂ, z ∈ (Set.univ : Set ℂ) → DifferentiableAt ℝ f z := by
        have hzero : ∀ᵐ z : ℂ, z ≠ 0 := by
          have hset : ({z : ℂ | ¬ (z ≠ 0)} : Set ℂ) = {0} := by ext z; simp
          rw [MeasureTheory.ae_iff, hset]
          simp
        filter_upwards [hzero] with z hz _
        exact hfdOff z hz
      have hbridge := WeakPartialEqFDerivAE Set.univ isOpen_univ f
        (fun j => if j = 0 then fx else fy) hfL
        (fun j => by
          fin_cases j
          · show MemLpLocOn 1 Set.univ fx
            exact hfxL
          · show MemLpLocOn 1 Set.univ fy
            exact hfyL)
        (fun j => by
          fin_cases j
          · show IsWeakPartialOn Set.univ 0 f fx
            exact hfw0
          · show IsWeakPartialOn Set.univ 1 f fy
            exact hfw1)
        hfdae
      filter_upwards [h12ae, hbridge 0, hbridge 1] with z h1 h2 h3 hz
      have e2 : fx z = fderiv ℝ f z 1 := h2 (Set.mem_univ z)
      have e3 : fy z = fderiv ℝ f z Complex.I := h3 (Set.mem_univ z)
      have eaf : af z = DZ f z := by rw [hafdef z, DZ, e2, e3]
      have ebf : bf z = DZbar f z := by rw [hbfdef z, DZbar, e2, e3]
      have h := h1 (Set.mem_univ z) (hfneOff z hz)
      rw [eaf, ebf] at h
      exact h
    intro z hz
    exact hdense _ isOpen_compl_singleton _ _ hDZbcont hRHSc hae z (by simpa using hz)
  have hfbreal : ∀ z : ℂ, z ≠ 0 → starRingEnd ℂ (DZbar f z) = DZbar f z := by
    intro z hz
    rw [h12pt z hz, map_mul, Complex.conj_ofReal, map_add, map_mul, map_mul,
      map_div₀, map_div₀, Complex.conj_conj, Complex.conj_conj]
    ring
  -- ## Step 14: the potential `v = 2 Re(z f z)/(d+1)`
  have hd1 : (0 : ℝ) < DExp p + 1 := by linarith
  obtain ⟨v, hvdef⟩ : ∃ u : ℂ → ℝ,
      u = fun z => (2 / (DExp p + 1)) * (z * f z).re := ⟨_, rfl⟩
  have hvC : ∀ z : ℂ, ((v z : ℝ) : ℂ)
      = ((1 / (DExp p + 1) : ℝ) : ℂ) * (z * f z + starRingEnd ℂ (z * f z)) := by
    intro z
    rw [hvdef]
    simp only
    rw [Complex.add_conj]
    push_cast
    field_simp
  have hvcont : Continuous v := by
    rw [hvdef]
    exact continuous_const.mul
      (Complex.continuous_re.comp (continuous_id.mul hfcont))
  have hvsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((v z : ℝ) : ℂ)) ({(0 : ℂ)}ᶜ) := by
    have heq : (fun z : ℂ => ((v z : ℝ) : ℂ))
        = fun z : ℂ => ((1 / (DExp p + 1) : ℝ) : ℂ)
            * (z * f z + starRingEnd ℂ (z * f z)) := funext hvC
    rw [heq]
    have hzf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => z * f z) ({(0 : ℂ)}ᶜ) :=
      contDiffOn_id.mul hfsm
    have hconjC : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℂ => starRingEnd ℂ y) :=
      Complex.conjLIE.toContinuousLinearEquiv.contDiff
    exact contDiffOn_const.mul (hzf.add (hconjC.comp_contDiffOn hzf))
  -- ## Step 13: Euler's identity, from the radial derivative computed two ways
  have heuler : ∀ z : ℂ, z ≠ 0 →
      z * DZ f z + starRingEnd ℂ z * DZbar f z = ((DExp p : ℝ) : ℂ) * f z := by
    intro z hz
    have hfd := hfdOff z hz
    have hline : HasDerivAt (fun t : ℝ => ((t : ℂ) * z)) z 1 := by
      have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 1 := Complex.ofRealCLM.hasDerivAt
      simpa using h1.mul_const z
    have hpt : ((1 : ℝ) : ℂ) * z = z := by push_cast; ring
    have h2 : HasFDerivAt f (fderiv ℝ f z) (((1 : ℝ) : ℂ) * z) := by
      rw [hpt]; exact hfd.hasFDerivAt
    have hA : HasDerivAt (fun t : ℝ => f ((t : ℂ) * z)) (fderiv ℝ f z z) 1 :=
      h2.comp_hasDerivAt 1 hline
    have hrp : HasDerivAt (fun t : ℝ => t ^ DExp p) (DExp p) 1 := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ DExp p)
          (DExp p * (1 : ℝ) ^ (DExp p - 1)) 1 := Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
      rw [Real.one_rpow, mul_one] at h1
      exact h1
    have hrpC : HasDerivAt (fun t : ℝ => ((t ^ DExp p : ℝ) : ℂ)) ((DExp p : ℝ) : ℂ) 1 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 hrp
    have hB : HasDerivAt (fun t : ℝ => f ((t : ℂ) * z)) (((DExp p : ℝ) : ℂ) * f z) 1 := by
      refine (hrpC.mul_const (f z)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
      exact hhom1 t ht.le z
    have huniq := hA.unique hB
    rw [hwform f z z] at huniq
    linear_combination huniq
  -- ## Step 14: `∂_z φ_v = f` off the origin
  have hDZc : ∀ (c : ℂ) (F : ℂ → ℂ) (u : ℂ), DifferentiableAt ℝ F u →
      DZ (fun y => c * F y) u = c * DZ F u := by
    intro c F u hF
    unfold DZ
    rw [fderiv_const_mul hF]
    simp only [smul_apply, smul_eq_mul]
    ring
  have hDZadd : ∀ (F G : ℂ → ℂ) (u : ℂ), DifferentiableAt ℝ F u → DifferentiableAt ℝ G u →
      DZ (fun y => F y + G y) u = DZ F u + DZ G u := by
    intro F G u hF hG
    unfold DZ
    rw [fderiv_fun_add hF hG]
    simp only [add_apply]
    ring
  have hDZid : ∀ u : ℂ, DZ (fun y : ℂ => y) u = 1 := by
    intro u; unfold DZ; simp; norm_num
  have hDZbid : ∀ u : ℂ, DZbar (fun y : ℂ => y) u = 0 := by
    intro u; unfold DZbar; simp
  have hvpot : ∀ z : ℂ, z ≠ 0 → DZ (fun u => ((v u : ℝ) : ℂ)) z = f z := by
    intro z hz
    have hfd := hfdOff z hz
    have hzf : DifferentiableAt ℝ (fun y : ℂ => y * f y) z :=
      (differentiable_id.differentiableAt).mul hfd
    have hconjD : DifferentiableAt ℝ (fun y : ℂ => starRingEnd ℂ (y * f y)) z :=
      (Complex.conjLIE.toContinuousLinearEquiv.differentiable.differentiableAt).comp z hzf
    -- the two Wirtinger derivatives of `z f z`
    obtain ⟨hp1, hp2⟩ := WirtingerProductRule (fun y : ℂ => y) f z
      differentiable_id.differentiableAt hfd
    rw [hDZid z] at hp1
    rw [hDZbid z] at hp2
    -- `∂_z conj(z f z) = conj(∂_z̄ (z f z))`, then `(12)` makes `f_z̄` real
    obtain ⟨hc1, -⟩ := WirtingerConjRule (fun y : ℂ => y * f y) z hzf
    have hcval : DZ (fun y : ℂ => starRingEnd ℂ (y * f y)) z
        = starRingEnd ℂ z * DZbar f z := by
      rw [hc1, hp2, show (0 : ℂ) * f z + z * DZbar f z = z * DZbar f z by ring,
        map_mul, hfbreal z hz]
    -- assemble
    -- the opaque-quotient dodge on the constant: carry its defining PRODUCT relation
    obtain ⟨c, hcdef⟩ : ∃ y : ℂ, y = ((1 / (DExp p + 1) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hcprod : c * (1 + ((DExp p : ℝ) : ℂ)) = 1 := by
      rw [hcdef]
      have h : ((DExp p + 1 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact hd1.ne'
      push_cast at h ⊢
      field_simp
      ring
    have heq : (fun u : ℂ => ((v u : ℝ) : ℂ))
        = fun u : ℂ => c * (u * f u + starRingEnd ℂ (u * f u)) := by
      funext u
      rw [hcdef]
      exact hvC u
    rw [heq, hDZc c (fun y : ℂ => y * f y + starRingEnd ℂ (y * f y)) z (hzf.add hconjD),
      hDZadd (fun y : ℂ => y * f y) (fun y : ℂ => starRingEnd ℂ (y * f y)) z hzf hconjD,
      hp1, hcval]
    have hE := heuler z hz
    linear_combination c * hE + f z * hcprod
  -- ## Steps 15, 16: `v` is `p`-harmonic on `ℂ`
  -- Step 15: the two first partials of `|f|^{p-2} f` are locally integrable
  have hwloc : ∀ j : Fin 2, MemLpLocOn 1 Set.univ
      (PartialWord [j] (fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ) * f ζ)) := by
    obtain ⟨w, hwdef⟩ : ∃ u : ℂ → ℂ, u = fun ζ : ℂ => ((‖f ζ‖ ^ (p - 2) : ℝ) : ℂ) * f ζ :=
      ⟨_, rfl⟩
    obtain ⟨κ, hκdef⟩ : ∃ y : ℝ, y = (p - 1) * DExp p := ⟨_, rfl⟩
    have hκ : 0 < κ := by rw [hκdef]; exact mul_pos (by linarith) hd
    have hfne : ∀ z : ℂ, z ≠ 0 → f z ≠ 0 := fun z hz hc => hz ((hfzero z).mp hc)
    -- `w` is `C^∞` off the origin
    have hwsmAt : ∀ ζ : ℂ, ζ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) w ζ := by
      intro ζ hζ
      have hfAt : ContDiffAt ℝ (⊤ : ℕ∞) f ζ :=
        hfsm.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hζ))
      have hmod : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ((‖z‖ ^ (p - 2) : ℝ) : ℂ)) (f ζ) :=
        (WirtingerModulusPowerRule (p - 2) (f ζ) (hfne ζ hζ)).1
      rw [hwdef]
      exact (hmod.comp ζ hfAt).mul hfAt
    have hwd : ∀ ζ : ℂ, ζ ≠ 0 → DifferentiableAt ℝ w ζ := fun ζ hζ =>
      (hwsmAt ζ hζ).differentiableAt (by norm_num)
    -- `w` is homogeneous of degree `κ = (p-1) d`
    have hwhom : ∀ t : ℝ, 0 < t → ∀ z : ℂ, w ((t : ℂ) * z) = ((t ^ κ : ℝ) : ℂ) * w z := by
      intro t ht z
      have h1 : ‖((t ^ DExp p : ℝ) : ℂ) * f z‖ = t ^ DExp p * ‖f z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
      have hreal : (t ^ DExp p * ‖f z‖) ^ (p - 2) * t ^ DExp p
          = t ^ κ * ‖f z‖ ^ (p - 2) := by
        rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (norm_nonneg _),
          ← Real.rpow_mul ht.le, mul_right_comm, ← Real.rpow_add ht, hκdef]
        ring_nf
      rw [hwdef]
      simp only
      rw [hhom1 t ht.le z, h1]
      have hrealC : (((t ^ DExp p * ‖f z‖) ^ (p - 2) * t ^ DExp p : ℝ) : ℂ)
          = ((t ^ κ * ‖f z‖ ^ (p - 2) : ℝ) : ℂ) := by rw [hreal]
      push_cast at hrealC ⊢
      linear_combination (f z) * hrealC
    -- differentiating the homogeneity identity
    have hder := hdilate w κ hwhom hwd
    intro j
    obtain ⟨e, hedef⟩ : ∃ y : ℂ, y = (if j = 0 then 1 else Complex.I) := ⟨_, rfl⟩
    have hpw : PartialWord [j] w = fun z : ℂ => fderiv ℝ w z e := by
      funext z
      rw [hedef]
      rfl
    rw [← hwdef, hpw]
    exact hradLp w κ hκ hwsmAt hder e
  have hph : PHarmonicOn p Set.univ v := by
    refine Eq12ImpliesPHarmonic p hp Set.univ isOpen_univ {(0 : ℂ)}
      (Set.subset_univ _) ?_ f v ?_ hfcont.continuousOn ?_ hf12
      ((Complex.continuous_ofReal.comp hvcont).continuousOn) ?_ ?_
      (hcontLp _ _ (Complex.continuous_ofReal.comp hvcont))
      (hcontLp _ _ hfcont) hwloc
    · intro Kc _ _
      exact Set.Finite.subset (Set.finite_singleton 0) Set.inter_subset_left
    · intro z _
      simpa using hfzero z
    · rw [hsetdiff]; exact hfsm
    · rw [hsetdiff]; exact hvsm
    · intro z hz
      rw [hsetdiff] at hz
      exact hvpot z (by simpa using hz)
  exact ⟨f, v, hfcont, hfH, hHf, hfsm, hhom1, hhom2, hvcont, hvsm, hph, hvpot⟩
