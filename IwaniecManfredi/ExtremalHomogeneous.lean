import IwaniecManfredi.ExtremalPolarForm
import IwaniecManfredi.DExpEqGammaOneInv
import IwaniecManfredi.PartialWord

/-- Homogeneity of the inverse of the extremal function: (57) of the paper,
`f(tz) = t^d f(z)` for `t ≥ 0`, and with it the homogeneity of degree
`d - |ν|` of every partial derivative `D^ν f`.  The two displays (58) and (59)
of Section 7 are the cases `|ν| = k-1` and `|ν| = k+1`, where `d = k-1+α`.
The proof is the paper's: the scaling identity `t H(ξ) = H(t^d ξ)` of (54),
composed with the inverse relation (55). -/
theorem ExtremalHomogeneous (p : ℝ) (hp : 1 < p) (f : ℂ → ℂ)
    (hfH : ∀ ξ : ℂ, f (ExtremalH p ξ) = ξ)
    (hHf : ∀ z : ℂ, ExtremalH p (f z) = z)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : ℂ)}ᶜ)) :
    (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
      f ((t : ℂ) * z) = ((t ^ DExp p : ℝ) : ℂ) * f z) ∧
    (∀ (w : List (Fin 2)) (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
      PartialWord w f ((t : ℂ) * z)
        = ((t ^ (DExp p - (w.length : ℝ)) : ℝ) : ℂ) * PartialWord w f z) := by
  obtain ⟨hg0, hgd⟩ := DExpEqGammaOneInv p hp
  have hd : 0 < DExp p := by
    rcases lt_trichotomy (DExp p) 0 with h | h | h
    · nlinarith
    · rw [h] at hgd; norm_num at hgd
    · exact h
  have hUopen : IsOpen ({(0 : ℂ)}ᶜ) := isOpen_compl_singleton
  -- (57) for t > 0
  have h57pos : ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      f ((t : ℂ) * z) = ((t ^ DExp p : ℝ) : ℂ) * f z := by
    intro t ht z
    have hscale := (ExtremalPolarForm p hp).2 t ht (f z)
    rw [hHf z] at hscale
    calc f ((t : ℂ) * z) = f (ExtremalH p (((t ^ DExp p : ℝ) : ℂ) * f z)) := by rw [← hscale]
      _ = ((t ^ DExp p : ℝ) : ℂ) * f z := hfH _
  -- (57) at t = 0
  have hf0 : f 0 = 0 := by
    have h := hfH 0
    have hH0 : ExtremalH p 0 = 0 := by unfold ExtremalH; simp
    rwa [hH0] at h
  have h57 : ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
      f ((t : ℂ) * z) = ((t ^ DExp p : ℝ) : ℂ) * f z := by
    intro t ht z
    rcases ht.lt_or_eq with h | h
    · exact h57pos t h z
    · rw [← h]
      simp [hf0, Real.zero_rpow hd.ne']
  refine ⟨h57, ?_⟩
  -- iterated partials of a smooth function are smooth on an open set
  have hPWcd : ∀ (w : List (Fin 2)) (g : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      ContDiffOn ℝ (⊤ : ℕ∞) g U → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w g) U := by
    intro w
    induction w with
    | nil => intro g U _ hg; exact hg
    | cons j w ih =>
        intro g U hU hg
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w g) U := ih g U hU hg
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w g)) U :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  have hfdiff : ∀ (w : List (Fin 2)) (z : ℂ), z ≠ 0 →
      DifferentiableAt ℝ (PartialWord w f) z := by
    intro w z hz
    exact ((hPWcd w f _ hUopen hsm).differentiableOn (by norm_num)).differentiableAt
      (hUopen.mem_nhds (by simpa using hz))
  intro w t ht z hz
  have htc : (t : ℂ) ≠ 0 := by simpa using ht.ne'
  have hfdscale : ∀ (g : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ g ((t : ℂ) * ζ) →
      ∀ v : ℂ, fderiv ℝ (fun y : ℂ => g ((t : ℂ) * y)) ζ v
        = (t : ℂ) * fderiv ℝ g ((t : ℂ) * ζ) v := by
    intro g ζ hg v
    have hsHFD : HasFDerivAt (fun y : ℂ => (t : ℂ) * y)
        ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ)) ζ :=
      (hasFDerivAt_id ζ).const_mul (t : ℂ)
    have hchain : HasFDerivAt (fun y : ℂ => g ((t : ℂ) * y))
        ((fderiv ℝ g ((t : ℂ) * ζ)).comp ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ))) ζ :=
      (hg.hasFDerivAt).comp ζ hsHFD
    have hsmv : ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ) v = (t : ℝ) • v := by
      simp [Complex.real_smul]
    rw [hchain.fderiv, ContinuousLinearMap.comp_apply, hsmv, map_smul, Complex.real_smul]
  -- Step 3: the dilation identity (1)
  have hdil : ∀ (w : List (Fin 2)) (ζ : ℂ), ζ ≠ 0 →
      PartialWord w (fun y : ℂ => f ((t : ℂ) * y)) ζ
        = (t : ℂ) ^ w.length * PartialWord w f ((t : ℂ) * ζ) := by
    intro w
    induction w with
    | nil => intro ζ _; simp [PartialWord]
    | cons j w ih =>
        intro ζ hζ
        have hζm : ζ ∈ (({(0 : ℂ)}ᶜ) : Set ℂ) := by simpa using hζ
        have htζ : (t : ℂ) * ζ ≠ 0 := mul_ne_zero htc hζ
        have hagree : ∀ y ∈ (({(0 : ℂ)}ᶜ) : Set ℂ),
            PartialWord w (fun y : ℂ => f ((t : ℂ) * y)) y
              = (t : ℂ) ^ w.length * PartialWord w f ((t : ℂ) * y) := by
          intro y hy; exact ih y (by simpa using hy)
        have hfe : fderiv ℝ (PartialWord w (fun y : ℂ => f ((t : ℂ) * y))) ζ
            = fderiv ℝ (fun y : ℂ => (t : ℂ) ^ w.length * PartialWord w f ((t : ℂ) * y)) ζ :=
          Filter.EventuallyEq.fderiv_eq
            (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hζm) hagree)
        have hR : fderiv ℝ (fun y : ℂ => (t : ℂ) ^ w.length * PartialWord w f ((t : ℂ) * y)) ζ
              (if j = 0 then (1 : ℂ) else Complex.I)
            = (t : ℂ) ^ (w.length + 1) * PartialWord (j :: w) f ((t : ℂ) * ζ) := by
          have hdiffinner : DifferentiableAt ℝ
              (fun y : ℂ => PartialWord w f ((t : ℂ) * y)) ζ := by
            have := (hfdiff w ((t : ℂ) * ζ) htζ)
            exact this.comp ζ (by fun_prop)
          rw [(hdiffinner.hasFDerivAt.const_mul ((t : ℂ) ^ w.length)).fderiv]
          simp only [smul_apply, smul_eq_mul]
          rw [hfdscale (PartialWord w f) ζ (hfdiff w _ htζ)]
          show (t : ℂ) ^ w.length * ((t : ℂ) * fderiv ℝ (PartialWord w f) ((t : ℂ) * ζ) _) = _
          rw [pow_succ]
          show _ = (t : ℂ) ^ w.length * (t : ℂ) * PartialWord (j :: w) f ((t : ℂ) * ζ)
          simp only [PartialWord, List.foldr]
          ring
        show fderiv ℝ (PartialWord w (fun y : ℂ => f ((t : ℂ) * y))) ζ
            (if j = 0 then (1 : ℂ) else Complex.I) = _
        rw [hfe, hR, List.length_cons]
  -- Step 4: constants pull out of PartialWord
  have hconst : ∀ (w : List (Fin 2)) (c : ℂ) (ζ : ℂ), ζ ≠ 0 →
      PartialWord w (fun y : ℂ => c * f y) ζ = c * PartialWord w f ζ := by
    intro w
    induction w with
    | nil => intro c ζ _; simp [PartialWord]
    | cons j w ih =>
        intro c ζ hζ
        have hζm : ζ ∈ (({(0 : ℂ)}ᶜ) : Set ℂ) := by simpa using hζ
        have hagree : ∀ y ∈ (({(0 : ℂ)}ᶜ) : Set ℂ),
            PartialWord w (fun y : ℂ => c * f y) y = c * PartialWord w f y := by
          intro y hy; exact ih c y (by simpa using hy)
        have hfe : fderiv ℝ (PartialWord w (fun y : ℂ => c * f y)) ζ
            = fderiv ℝ (fun y : ℂ => c * PartialWord w f y) ζ :=
          Filter.EventuallyEq.fderiv_eq
            (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hζm) hagree)
        show fderiv ℝ (PartialWord w (fun y : ℂ => c * f y)) ζ
            (if j = 0 then (1 : ℂ) else Complex.I) = _
        rw [hfe, ((hfdiff w ζ hζ).hasFDerivAt.const_mul c).fderiv]
        simp only [smul_apply, smul_eq_mul]
        simp only [PartialWord, List.foldr]
  -- combine
  have heqfun : (fun y : ℂ => f ((t : ℂ) * y))
      = fun y : ℂ => ((t ^ DExp p : ℝ) : ℂ) * f y := funext fun y => h57 t ht.le y
  have hkey : (t : ℂ) ^ w.length * PartialWord w f ((t : ℂ) * z)
      = ((t ^ DExp p : ℝ) : ℂ) * PartialWord w f z := by
    rw [← hdil w z hz, heqfun, hconst w _ z hz]
  have htl : ((t ^ (w.length : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ w.length := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  have hsub : ((t ^ (DExp p - (w.length : ℝ)) : ℝ) : ℂ)
      = ((t ^ DExp p : ℝ) : ℂ) / (t : ℂ) ^ w.length := by
    rw [Real.rpow_sub ht, ← htl]
    push_cast
    ring
  rw [hsub, div_mul_eq_mul_div, ← hkey]
  field_simp
