import IwaniecManfredi.SolvesEq12
import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.ChiFirstDerivs
import IwaniecManfredi.WirtingerPowerRule
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.WeakPartialEqFDerivAE

/-- The hodograph step of Section 3 of the paper: if `f` solves (12) and
factors as `f = χ^n` with `χ` injective and `χ(z₀) = 0` at the singular point
`z₀`, then the inverse
`H` of `χ` solves the *linear* system (18).  This is the paper's
"From (16) we see that `H` satisfies the linear equation (18)"
(`paper.tex:179-181`), with (16) obtained from (12) by the power rule and (18)
from (16) by the inverse-derivative formulas (17).  It is the only bridge
between the `f`-side of the development, where (12) lives, and the `H`-side,
where Theorem 2 and Corollary 1 live.

The `H`-side hypotheses are exactly what (17) and the weak form of (18)
consume: `H ∈ W^{1,2}_loc(V)`, differentiability almost everywhere and
`Jac H ≠ 0` almost everywhere, all three of which item (C2) of the paper's
note supplies for the inverse of a quasiconformal homeomorphism -- its clause
reads "the inverse `H` of a quasiconformal homeomorphism belongs to
`W^{1,2}_loc`, has Jacobian `J > 0` almost everywhere, and satisfies (17)".
The Sobolev clause is what makes the conclusion statable at all: by
`SolvesEq18` solving (18) is an identity between the *weak* Wirtinger
derivatives of `H`, which exist precisely because `H` lies in a local Sobolev
space.  No smoothness of `H` is assumed -- the paper's arrow runs `H → χ` and
`H`'s regularity is produced only later, from (18) itself, so assuming it here
would invert the development. -/
theorem HodographEq18 (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (W V : Set ℂ) (hW : IsOpen W) (hV : IsOpen V) (z₀ : ℂ) (hz₀W : z₀ ∈ W)
    (f chi H : ℂ → ℂ)
    (hfact : ∀ z ∈ W, f z = chi z ^ n)
    (hchi0 : chi z₀ = 0) (hinj : Set.InjOn chi W)
    (hchism : ContDiffOn ℝ (⊤ : ℕ∞) chi (W \ {z₀}))
    (hHW : MemWLocOn 1 2 V H)
    (hHdiff : ∀ᵐ ξ : ℂ, ξ ∈ V → DifferentiableAt ℝ H ξ)
    (hHJ : ∀ᵐ ξ : ℂ, ξ ∈ V → Jac H ξ ≠ 0)
    (himg : ∀ ξ ∈ V, H ξ ∈ W) (hinv : ∀ ξ ∈ V, chi (H ξ) = ξ) (hH0 : H 0 = z₀)
    (h12 : SolvesEq12 p W f) :
    SolvesEq18 n p V H := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hWo : IsOpen (W \ {z₀}) := hW.sdiff isClosed_singleton
  -- ## Shared tool: `L²_loc ⊆ L¹_loc`
  have hL21 : ∀ (S : Set ℂ) (u : ℂ → ℂ), MemLpLocOn 2 S u → MemLpLocOn 1 S u := by
    intro S u hu K hKsub hK
    refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top (hu K hKsub hK) ?_
      hK.measure_lt_top.ne (by norm_num)
    intro x hx
    exact Set.indicator_of_notMem hx u
  -- ## Shared tool: an a.e. identity between functions continuous on an open set is pointwise
  have hagree : ∀ (S : Set ℂ), IsOpen S → ∀ F G : ℂ → ℂ, ContinuousOn F S → ContinuousOn G S →
      (∀ᵐ z : ℂ, z ∈ S → F z = G z) → ∀ z ∈ S, F z = G z := by
    intro S hS F G hF hG hae z hz
    by_contra hne
    have hEopen : IsOpen {x : ℂ | x ∈ S ∧ F x ≠ G x} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨hxmem, hxne⟩ := hx
      have hd : ContinuousAt (fun y => F y - G y) x :=
        (hF.continuousAt (hS.mem_nhds hxmem)).sub (hG.continuousAt (hS.mem_nhds hxmem))
      filter_upwards [hS.mem_nhds hxmem, hd.eventually_ne (sub_ne_zero.mpr hxne)]
        with y hy1 hy2
      exact ⟨hy1, sub_ne_zero.mp hy2⟩
    have hE0 : MeasureTheory.volume {x : ℂ | x ∈ S ∧ F x ≠ G x} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hcon
      exact hx.2 (hcon hx.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨z, hz, hne⟩).ne' hE0
  -- ## Shared tool: `DZ`/`DZbar` see a function only through its values on an open set
  have hdzc : ∀ (S : Set ℂ), IsOpen S → ∀ (f₁ f₂ : ℂ → ℂ) (z : ℂ), z ∈ S →
      (∀ ζ ∈ S, f₁ ζ = f₂ ζ) → DZ f₁ z = DZ f₂ z ∧ DZbar f₁ z = DZbar f₂ z := by
    intro S hS f₁ f₂ z hz h
    have hev : f₁ =ᶠ[nhds z] f₂ := by
      filter_upwards [hS.mem_nhds hz] with ζ hζ using h ζ hζ
    exact ⟨by rw [DZ, DZ, hev.fderiv_eq], by rw [DZbar, DZbar, hev.fderiv_eq]⟩
  -- ## Shared tool: continuity of the Wirtinger derivatives of a `C^∞` function
  have hdzcont : ∀ (S : Set ℂ), IsOpen S → ∀ u : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u S →
      ContinuousOn (DZ u) S ∧ ContinuousOn (DZbar u) S := by
    intro S hS u hu
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ u z) S :=
      hu.fderiv_of_isOpen hS (by simp)
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ u z 1) S :=
      hfd.clm_apply contDiffOn_const
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ u z Complex.I) S :=
      hfd.clm_apply contDiffOn_const
    have e1 : DZ u
        = fun z => (1 / 2 : ℂ) * (fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I) := rfl
    have e2 : DZbar u
        = fun z => (1 / 2 : ℂ) * (fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I) := rfl
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact (contDiffOn_const.mul (h1.sub (contDiffOn_const.mul h2))).continuousOn
    · rw [e2]
      exact (contDiffOn_const.mul (h1.add (contDiffOn_const.mul h2))).continuousOn
  -- ## Step 1: `chi` and `f` do not vanish on `W - {z₀}`
  have hchine : ∀ z ∈ W \ {z₀}, chi z ≠ 0 := by
    intro z hz hc
    exact hz.2 (hinj hz.1 hz₀W (by rw [hc, hchi0]))
  have hfne : ∀ z ∈ W \ {z₀}, f z ≠ 0 := by
    intro z hz
    rw [hfact z hz.1]
    exact pow_ne_zero _ (hchine z hz)
  have hgsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => chi z ^ (m + 1)) (W \ {z₀}) := hchism.pow (m + 1)
  have hfsm : ContDiffOn ℝ (⊤ : ℕ∞) f (W \ {z₀}) :=
    hgsm.congr (fun z hz => hfact z hz.1)
  -- ## Step 2: (12) at EVERY point of `W - {z₀}`
  obtain ⟨af, bf, hwwf, h12ae⟩ := h12
  obtain ⟨fx, fy, hfL1, hfxL1, hfyL1, hwp0f, hwp1f, hafdef, hbfdef⟩ := hwwf
  have hfdiffae : ∀ᵐ z : ℂ, z ∈ W → DifferentiableAt ℝ f z := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton z₀)
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    by_contra hzz
    refine hz ?_
    intro hzW
    exact (hfsm.differentiableOn (by simp)).differentiableAt
      (hWo.mem_nhds ⟨hzW, by simpa using hzz⟩)
  have hfwpae := WeakPartialEqFDerivAE W hW f (fun j => if j = 0 then fx else fy) hfL1
    (by intro j; by_cases hj : j = 0 <;> simp [hj, hfxL1, hfyL1])
    (by
      intro j
      by_cases hj : j = 0
      · subst hj; simpa using hwp0f
      · have hj1 : j = 1 := by omega
        subst hj1; simpa using hwp1f)
    hfdiffae
  have h12ae' : ∀ᵐ z : ℂ, z ∈ W \ {z₀} → DZbar f z
      = ((1 / p - 1 / 2 : ℝ) : ℂ) * ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)) := by
    filter_upwards [h12ae, hfwpae 0, hfwpae 1] with z hz h0 h1
    intro hzm
    have e0 : fx z = fderiv ℝ f z 1 := by simpa [PartialWord] using h0 hzm.1
    have e1 : fy z = fderiv ℝ f z Complex.I := by simpa [PartialWord] using h1 hzm.1
    have ea : af z = DZ f z := by rw [hafdef z, e0, e1, DZ]
    have eb : bf z = DZbar f z := by rw [hbfdef z, e0, e1, DZbar]
    have := hz hzm.1 (hfne z hzm)
    rw [ea, eb] at this
    exact this
  have hfc : ContinuousOn f (W \ {z₀}) := hfsm.continuousOn
  have hcfc : ContinuousOn (fun z => starRingEnd ℂ (f z)) (W \ {z₀}) :=
    Complex.continuous_conj.comp_continuousOn hfc
  have hcfne : ∀ z ∈ W \ {z₀}, starRingEnd ℂ (f z) ≠ 0 := by
    intro z hz
    simpa using hfne z hz
  obtain ⟨hDZc, hDZbc⟩ := hdzcont (W \ {z₀}) hWo f hfsm
  have hRHSc : ContinuousOn (fun z => ((1 / p - 1 / 2 : ℝ) : ℂ)
      * ((starRingEnd ℂ (f z) / f z) * DZ f z
          + (f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z))) (W \ {z₀}) :=
    continuousOn_const.mul (((hcfc.div hfc hfne).mul hDZc).add
      ((hfc.div hcfc hcfne).mul (Complex.continuous_conj.comp_continuousOn hDZc)))
  have h12pt := hagree (W \ {z₀}) hWo _ _ hDZbc hRHSc h12ae'
  -- ## Step 6: the weak Wirtinger witness for `H`
  obtain ⟨DH, hDH0, hDHL2, hDHwp⟩ := hHW
  obtain ⟨Hx, hHxd⟩ : ∃ g : ℂ → ℂ, g = DH [0] := ⟨_, rfl⟩
  obtain ⟨Hy, hHyd⟩ : ∃ g : ℂ → ℂ, g = DH [1] := ⟨_, rfl⟩
  have hHL1 : MemLpLocOn 1 V H := by
    refine hL21 V H ?_
    rw [← hDH0]
    exact hDHL2 [] (by simp)
  have hHxL1 : MemLpLocOn 1 V Hx := by
    refine hL21 V Hx ?_
    rw [hHxd]
    exact hDHL2 [0] (by simp)
  have hHyL1 : MemLpLocOn 1 V Hy := by
    refine hL21 V Hy ?_
    rw [hHyd]
    exact hDHL2 [1] (by simp)
  have hwp0H : IsWeakPartialOn V 0 H Hx := by
    have h := hDHwp [] 0 (by simp)
    rw [hDH0] at h
    rw [hHxd]
    simpa using h
  have hwp1H : IsWeakPartialOn V 1 H Hy := by
    have h := hDHwp [] 1 (by simp)
    rw [hDH0] at h
    rw [hHyd]
    simpa using h
  have hHwpae := WeakPartialEqFDerivAE V hV H (fun j => if j = 0 then Hx else Hy) hHL1
    (by intro j; by_cases hj : j = 0 <;> simp [hj, hHxL1, hHyL1])
    (by
      intro j
      by_cases hj : j = 0
      · subst hj; simpa using hwp0H
      · have hj1 : j = 1 := by omega
        subst hj1; simpa using hwp1H)
    hHdiff
  refine ⟨fun z => (1 / 2 : ℂ) * (Hx z - Complex.I * Hy z),
    fun z => (1 / 2 : ℂ) * (Hx z + Complex.I * Hy z),
    ⟨Hx, Hy, hHL1, hHxL1, hHyL1, hwp0H, hwp1H, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  -- ## Steps 4 and 5: (18) off a null set
  filter_upwards [hHdiff, hHJ, hHwpae 0, hHwpae 1] with ξ hd hj h0 h1
  intro hξV hξne
  have hdξ := hd hξV
  have hjξ := hj hξV
  have ex0 : Hx ξ = fderiv ℝ H ξ 1 := by simpa [PartialWord] using h0 hξV
  have ex1 : Hy ξ = fderiv ℝ H ξ Complex.I := by simpa [PartialWord] using h1 hξV
  obtain ⟨A, hA⟩ : ∃ x : ℂ, x = DZ H ξ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x : ℂ, x = DZbar H ξ := ⟨_, rfl⟩
  obtain ⟨J, hJd⟩ : ∃ x : ℂ, x = ((Jac H ξ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hJne : J ≠ 0 := by
    rw [hJd]
    exact Complex.ofReal_ne_zero.mpr hjξ
  have hJreal : starRingEnd ℂ J = J := by
    rw [hJd]
    exact Complex.conj_ofReal _
  have hXcne : starRingEnd ℂ ξ ≠ 0 := by
    simpa using hξne
  -- Step 4: `H ξ ∈ W - {z₀}`
  have hzW : H ξ ∈ W := himg ξ hξV
  have hchiz : chi (H ξ) = ξ := hinv ξ hξV
  have hzne : H ξ ≠ z₀ := by
    intro hc
    exact hξne (by rw [← hchiz, hc, hchi0])
  have hzm : H ξ ∈ W \ {z₀} := ⟨hzW, by simpa using hzne⟩
  have hchid : DifferentiableAt ℝ chi (H ξ) :=
    (hchism.differentiableOn (by simp)).differentiableAt (hWo.mem_nhds hzm)
  -- (17)
  obtain ⟨h17a, h17b⟩ := ChiFirstDerivs V hV chi H ξ hξV hinv hdξ hchid hjξ
  rw [← hA, ← hJd] at h17a
  rw [← hB, ← hJd] at h17b
  -- the power rule at `H ξ`
  have hNe : (((m + 1 : ℕ) : ℤ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hEx : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
  have hpowm : chi (H ξ) ^ (((m + 1 : ℕ) : ℤ) - 1) = ξ ^ m := by
    rw [hchiz, hEx, zpow_natCast]
  obtain ⟨hpw1, hpw2⟩ := WirtingerPowerRule chi (W \ {z₀}) hWo hchism hchine
    (((m + 1 : ℕ) : ℤ)) (H ξ) hzm
  have hfeq : ∀ ζ ∈ W \ {z₀}, f ζ = chi ζ ^ (((m + 1 : ℕ) : ℤ)) := by
    intro ζ hζ
    rw [hfact ζ hζ.1, zpow_natCast]
  obtain ⟨hcf1, hcf2⟩ := hdzc (W \ {z₀}) hWo f (fun w => chi w ^ (((m + 1 : ℕ) : ℤ)))
    (H ξ) hzm hfeq
  have hDZf : DZ f (H ξ) = ((m : ℂ) + 1) * ξ ^ m * (starRingEnd ℂ A / J) := by
    rw [hcf1, hpw1, hNe, hpowm, h17a]
  have hDZbf : DZbar f (H ξ) = ((m : ℂ) + 1) * ξ ^ m * (-B / J) := by
    rw [hcf2, hpw2, hNe, hpowm, h17b]
  have hfz : f (H ξ) = ξ ^ (m + 1) := by rw [hfact _ hzW, hchiz]
  -- (12) at `z = H ξ`
  obtain ⟨cp, hcp⟩ : ∃ x : ℂ, x = ((1 / p - 1 / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have E12 := h12pt (H ξ) hzm
  rw [hDZf, hDZbf, hfz, ← hcp] at E12
  simp only [map_mul, map_div₀, map_pow, map_add, map_one, Complex.conj_natCast,
    Complex.conj_conj, hJreal] at E12
  -- the goal
  show (1 / 2 : ℂ) * (Hx ξ + Complex.I * Hy ξ)
      = ((1 / 2 - 1 / p : ℝ) : ℂ)
        * ((ξ / starRingEnd ℂ ξ) * ((1 / 2 : ℂ) * (Hx ξ - Complex.I * Hy ξ))
          + ((starRingEnd ℂ ξ) ^ (m + 1) / ξ ^ (m + 1))
              * starRingEnd ℂ ((1 / 2 : ℂ) * (Hx ξ - Complex.I * Hy ξ)))
  have hAdef : A = (1 / 2 : ℂ) * (Hx ξ - Complex.I * Hy ξ) := by
    rw [hA, ex0, ex1, DZ]
  have hBdef : B = (1 / 2 : ℂ) * (Hx ξ + Complex.I * Hy ξ) := by
    rw [hB, ex0, ex1, DZbar]
  rw [← hAdef, ← hBdef]
  have hcc : ((1 / 2 - 1 / p : ℝ) : ℂ) = -((1 / p - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcc, ← hcp]
  have hmne : ((m : ℂ) + 1) ≠ 0 := by
    have h : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact Nat.cast_ne_zero.mpr (by omega)
  field_simp at E12
  have hfac : (ξ ^ m * starRingEnd ℂ ξ ^ m) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hξne) (pow_ne_zero _ hXcne)
  have hcontent : B * (ξ ^ (m + 1) * starRingEnd ℂ ξ)
      = -cp * (ξ ^ (m + 2) * A + starRingEnd ℂ ξ ^ (m + 2) * starRingEnd ℂ A) := by
    refine mul_left_cancel₀ hfac ?_
    linear_combination -E12
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (m + 1) hξne) hXcne) ?_
  rw [hcontent]
  field_simp
  ring
