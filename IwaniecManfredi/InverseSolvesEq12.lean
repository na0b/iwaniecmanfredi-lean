import IwaniecManfredi.SolvesEq12
import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.ChiFirstDerivs
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.WeakPartialEqFDerivAE

/-- The converse hodograph step, which Section 7 needs and which
`HodographEq18` does not supply: a solution of the *linear* system (18) at
`n = 1` has an inverse solving the nonlinear equation (12).  `HodographEq18`
runs the arrow `f ↦ H`, consuming (12) and producing (18); here the arrow runs
`H ↦ f`, because Section 7 starts from the explicit solution (54) of (18) and
must know that its inverse is the complex gradient of a `p`-harmonic function
(`paper.tex:113`, `paper.tex:592`).

`ChiFirstDerivs` is stated so that it applies with the roles of the two
mutually inverse maps exchanged, which is exactly the direction used here: it
turns `H_ξ`, `H_ξ̄` into `f_z`, `f_z̄`, and then (18) at `n = 1` becomes (12),
the two coefficient brackets matching only at `n = 1`.  Smoothness of `H` off
the origin is assumed because it is what upgrades the almost-everywhere (18)
to a pointwise identity; the pointwise form is what the exchange of roles
consumes, and no measure-theoretic transport of the exceptional set under `H`
is then needed.

`MemWLocOn 1 1 (H '' V) f` is assumed because the conclusion needs it and
needs nothing more: by `SolvesEq12`, solving (12) is an identity between the
*weak* Wirtinger derivatives of `f`, and `W^{1,1}_loc` is exactly the data
those consist of.  For the `f` of Section 7 it comes from the explicit
homogeneity of the inverse of (54), and in general from (C1), which puts the
complex gradient of a `p`-harmonic function in `W^{1,2}_loc ⊆ W^{1,1}_loc`. -/
theorem InverseSolvesEq12 (p : ℝ) (hp : 1 < p) (V : Set ℂ) (hV : IsOpen V)
    (H f : ℂ → ℂ) (hVimg : IsOpen (H '' V))
    (hHsm : ContDiffOn ℝ (1 : ℕ) H (V \ {0}))
    (h18 : SolvesEq18 1 p V H)
    (hinv : ∀ ξ ∈ V, f (H ξ) = ξ)
    (hfW : MemWLocOn 1 1 (H '' V) f)
    (hfdiff : ∀ᵐ z : ℂ, z ∈ H '' V → DifferentiableAt ℝ f z)
    (hfJ : ∀ᵐ z : ℂ, z ∈ H '' V → Jac f z ≠ 0) :
    SolvesEq12 p (H '' V) f := by
  -- ## Step 1: the inverse relations on `H '' V`
  have hinv1 : ∀ ζ ∈ H '' V, H (f ζ) = ζ ∧ f ζ ∈ V := by
    intro ζ hζ
    obtain ⟨ξ, hξV, hξ⟩ := hζ
    have hfz : f ζ = ξ := by rw [← hξ]; exact hinv ξ hξV
    exact ⟨by rw [hfz, hξ], by rw [hfz]; exact hξV⟩
  -- ## Step 2: (18) holds at EVERY point of `V - {0}`
  have hV0 : IsOpen (V \ {0}) := hV.sdiff isClosed_singleton
  have hHdiffOn : ∀ ξ ∈ V \ {0}, DifferentiableAt ℝ H ξ := by
    intro ξ hξ
    exact (hHsm.differentiableOn (by norm_num)).differentiableAt (hV0.mem_nhds hξ)
  have hane : ∀ᵐ z : ℂ, z ≠ 0 := by
    have hset : ({z : ℂ | ¬ (z ≠ 0)} : Set ℂ) = {0} := by ext z; simp
    rw [MeasureTheory.ae_iff, hset]
    simp
  have hHae : ∀ᵐ ξ : ℂ, ξ ∈ V → DifferentiableAt ℝ H ξ := by
    filter_upwards [hane] with ξ hξ hξV
    exact hHdiffOn ξ ⟨hξV, by simpa using hξ⟩
  obtain ⟨aH, bH, hWW, h18ae⟩ := h18
  obtain ⟨Hx, Hy, hHL, hHxL, hHyL, hHw0, hHw1, haHdef, hbHdef⟩ := hWW
  have hbridgeH := WeakPartialEqFDerivAE V hV H (fun j => if j = 0 then Hx else Hy) hHL
    (fun j => by
      fin_cases j
      · show MemLpLocOn 1 V Hx
        exact hHxL
      · show MemLpLocOn 1 V Hy
        exact hHyL)
    (fun j => by
      fin_cases j
      · show IsWeakPartialOn V 0 H Hx
        exact hHw0
      · show IsWeakPartialOn V 1 H Hy
        exact hHw1)
    hHae
  have h18pt : ∀ᵐ ξ : ℂ, ξ ∈ V → ξ ≠ 0 →
      DZbar H ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * DZ H ξ
          + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ H ξ)) := by
    filter_upwards [h18ae, hbridgeH 0, hbridgeH 1] with ξ h1 h2 h3 hξV hξ0
    have e2 : Hx ξ = fderiv ℝ H ξ 1 := h2 hξV
    have e3 : Hy ξ = fderiv ℝ H ξ Complex.I := h3 hξV
    have eaH : aH ξ = DZ H ξ := by rw [haHdef ξ, DZ, e2, e3]
    have ebH : bH ξ = DZbar H ξ := by rw [hbHdef ξ, DZbar, e2, e3]
    have h := h1 hξV hξ0
    rw [eaH, ebH] at h
    simpa using h
  -- continuity of both sides of (18) on the open set `V - {0}`
  have hfdc : ContinuousOn (fderiv ℝ H) (V \ {0}) :=
    hHsm.continuousOn_fderiv_of_isOpen hV0 (by norm_num)
  have hev : ∀ v : ℂ, ContinuousOn (fun ξ => fderiv ℝ H ξ v) (V \ {0}) := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp_continuousOn hfdc
  have hDZc : ContinuousOn (fun ξ => DZ H ξ) (V \ {0}) := by
    unfold DZ
    exact continuousOn_const.mul ((hev 1).sub (continuousOn_const.mul (hev Complex.I)))
  have hDZbc : ContinuousOn (fun ξ => DZbar H ξ) (V \ {0}) := by
    unfold DZbar
    exact continuousOn_const.mul ((hev 1).add (continuousOn_const.mul (hev Complex.I)))
  have hcjc : ContinuousOn (fun ξ : ℂ => starRingEnd ℂ ξ) (V \ {0}) :=
    Complex.continuous_conj.continuousOn
  have hcjne : ∀ ξ ∈ V \ {0}, starRingEnd ℂ ξ ≠ 0 := by
    intro ξ hξ
    have : ξ ≠ 0 := by simpa using hξ.2
    simpa using this
  have hidne : ∀ ξ ∈ V \ {0}, (ξ : ℂ) ≠ 0 := fun ξ hξ => by simpa using hξ.2
  have hRHSc : ContinuousOn (fun ξ : ℂ => ((1 / 2 - 1 / p : ℝ) : ℂ) *
      ((ξ / starRingEnd ℂ ξ) * DZ H ξ
        + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ H ξ))) (V \ {0}) := by
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact (continuousOn_id.div hcjc hcjne).mul hDZc
    · exact (hcjc.div continuousOn_id hidne).mul (Complex.continuous_conj.comp_continuousOn hDZc)
  -- a.e. agreement plus continuity on an open set forces agreement everywhere
  have hdense : ∀ (W : Set ℂ), IsOpen W → ∀ (F G : ℂ → ℂ), ContinuousOn F W → ContinuousOn G W →
      (∀ᵐ z : ℂ, z ∈ W → F z = G z) → ∀ z ∈ W, F z = G z := by
    intro W hW F G hF hG hae z hz
    by_contra hne
    have hEopen : IsOpen {x : ℂ | x ∈ W ∧ F x ≠ G x} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨hxmem, hxne⟩ := hx
      have hd : ContinuousAt (fun y => F y - G y) x :=
        (hF.continuousAt (hW.mem_nhds hxmem)).sub (hG.continuousAt (hW.mem_nhds hxmem))
      filter_upwards [hW.mem_nhds hxmem, hd.eventually_ne (sub_ne_zero.mpr hxne)]
        with y hy1 hy2
      exact ⟨hy1, sub_ne_zero.mp hy2⟩
    have hE0 : MeasureTheory.volume {x : ℂ | x ∈ W ∧ F x ≠ G x} = 0 := by
      refine MeasureTheory.measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq]
      intro hcon
      exact hx.2 (hcon hx.1)
    exact (IsOpen.measure_pos MeasureTheory.volume hEopen ⟨z, hz, hne⟩).ne' hE0
  have h18every : ∀ ξ ∈ V \ {0}, DZbar H ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
      ((ξ / starRingEnd ℂ ξ) * DZ H ξ
        + ((starRingEnd ℂ ξ) / ξ) * starRingEnd ℂ (DZ H ξ)) := by
    refine hdense (V \ {0}) hV0 _ _ hDZbc hRHSc ?_
    filter_upwards [h18pt] with ξ h hξ
    exact h hξ.1 (by simpa using hξ.2)
  -- ## Step 6: the weak Wirtinger pair of `f`, from `MemWLocOn 1 1 (H '' V) f`
  obtain ⟨D, hD0, hDL, hDw⟩ := hfW
  have hfL : MemLpLocOn 1 (H '' V) f := by rw [← hD0]; exact hDL [] (by simp)
  have hw0 : IsWeakPartialOn (H '' V) 0 f (D [0]) := by
    have h := hDw [] 0 (by simp)
    rw [hD0] at h
    simpa using h
  have hw1 : IsWeakPartialOn (H '' V) 1 f (D [1]) := by
    have h := hDw [] 1 (by simp)
    rw [hD0] at h
    simpa using h
  obtain ⟨a, hadef⟩ : ∃ g : ℂ → ℂ,
      g = fun z => (1 / 2 : ℂ) * (D [0] z - Complex.I * D [1] z) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ g : ℂ → ℂ,
      g = fun z => (1 / 2 : ℂ) * (D [0] z + Complex.I * D [1] z) := ⟨_, rfl⟩
  have hWWf : IsWeakWirtingerOn (H '' V) f a b :=
    ⟨D [0], D [1], hfL, hDL [0] (by simp), hDL [1] (by simp), hw0, hw1,
      fun z => by rw [hadef], fun z => by rw [hbdef]⟩
  have hbridgeF := WeakPartialEqFDerivAE (H '' V) hVimg f (fun j => D [j]) hfL
    (fun j => hDL [j] (by simp))
    (fun j => by
      fin_cases j
      · show IsWeakPartialOn (H '' V) 0 f (D [0])
        exact hw0
      · show IsWeakPartialOn (H '' V) 1 f (D [1])
        exact hw1)
    hfdiff
  refine ⟨a, b, hWWf, ?_⟩
  -- ## Steps 3, 4 and 5: at almost every `z`, the inverse-derivative formulas turn (18) into (12)
  filter_upwards [hfdiff, hfJ, hbridgeF 0, hbridgeF 1] with z hdz hJz h0 h1 hzU hfz
  have e0 : D [0] z = fderiv ℝ f z 1 := h0 hzU
  have e1 : D [1] z = fderiv ℝ f z Complex.I := h1 hzU
  have ea : a z = DZ f z := by rw [hadef]; simp only; rw [DZ, e0, e1]
  have eb : b z = DZbar f z := by rw [hbdef]; simp only; rw [DZbar, e0, e1]
  -- the good point: `f z ∈ V - {0}`, `H` differentiable there, `Jac f z ≠ 0`
  obtain ⟨hHfz, hfzV⟩ := hinv1 z hzU
  have hfzV0 : f z ∈ V \ {0} := ⟨hfzV, by simpa using hfz⟩
  have hHd : DifferentiableAt ℝ H (f z) := hHdiffOn (f z) hfzV0
  have hJ : Jac f z ≠ 0 := hJz hzU
  have hJc : ((Jac f z : ℝ) : ℂ) ≠ 0 := by simpa using hJ
  obtain ⟨hc1, hc2⟩ := ChiFirstDerivs (H '' V) hVimg H f z hzU
    (fun ζ hζ => (hinv1 ζ hζ).1) (hdz hzU) hHd hJ
  have hc3 : starRingEnd ℂ (DZ H (f z)) = DZ f z / ((Jac f z : ℝ) : ℂ) := by
    rw [hc1, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
  -- (18) at `f z`, with the three substitutions
  have h18z := h18every (f z) hfzV0
  rw [hc3, hc1, hc2] at h18z
  have hcne : starRingEnd ℂ (f z) ≠ 0 := by simpa using hfz
  -- clear the Jacobian: both sides carry exactly one factor `1 / Jac f z`
  have hstep : -(DZbar f z) / ((Jac f z : ℝ) : ℂ)
      = (((1 / 2 - 1 / p : ℝ) : ℂ) * ((f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)
          + (starRingEnd ℂ (f z) / f z) * DZ f z)) / ((Jac f z : ℝ) : ℂ) := by
    rw [h18z]; ring
  have hcancel : -(DZbar f z)
      = ((1 / 2 - 1 / p : ℝ) : ℂ) * ((f z / starRingEnd ℂ (f z)) * starRingEnd ℂ (DZ f z)
          + (starRingEnd ℂ (f z) / f z) * DZ f z) := by
    rw [div_eq_div_iff hJc hJc] at hstep
    exact mul_right_cancel₀ hJc hstep
  have hccast : ((1 / p - 1 / 2 : ℝ) : ℂ) = -((1 / 2 - 1 / p : ℝ) : ℂ) := by push_cast; ring
  rw [ea, eb, hccast]
  linear_combination -hcancel
