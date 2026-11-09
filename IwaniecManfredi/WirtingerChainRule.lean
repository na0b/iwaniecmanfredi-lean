import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar

/-- The chain rule for the Wirtinger operators:
`∂(F∘G)/∂ξ = F_z(G) G_ξ + F_z̄(G) conj(G_ξ̄)` and
`∂(F∘G)/∂ξ̄ = F_z(G) G_ξ̄ + F_z̄(G) conj(G_ξ)`.  Applied to `F = D^ν χ` and
`G = H` this is the pair of equations displayed in the proof of Lemma 1 of the
paper. -/
theorem WirtingerChainRule (F G : ℂ → ℂ) (ξ : ℂ)
    (hG : DifferentiableAt ℝ G ξ) (hF : DifferentiableAt ℝ F (G ξ)) :
    DZ (fun z => F (G z)) ξ
        = DZ F (G ξ) * DZ G ξ + DZbar F (G ξ) * starRingEnd ℂ (DZbar G ξ) ∧
      DZbar (fun z => F (G z)) ξ
        = DZ F (G ξ) * DZbar G ξ + DZbar F (G ξ) * starRingEnd ℂ (DZ G ξ) := by
  -- The shared Wirtinger-decomposition brick, inlined as a `have` rather than
  -- promoted to a helper node (FILESPEC:126-129 makes that promotion a later
  -- proof-body edit, so deferring it costs nothing).  Quantified over the map
  -- and both points so the three use sites below rewrite as in the probe.
  have hdecomp : ∀ (H : ℂ → ℂ) (w v : ℂ),
      fderiv ℝ H w v = DZ H w * v + DZbar H w * (starRingEnd ℂ v) := by
    intro H w v
    obtain ⟨x, y, hvv⟩ : ∃ x y : ℝ, v = (x : ℂ) + (y : ℂ) * Complex.I :=
      ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
    subst hvv
    have hx : fderiv ℝ H w ((x : ℂ) + (y : ℂ) * Complex.I)
        = (x : ℝ) • fderiv ℝ H w 1 + (y : ℝ) • fderiv ℝ H w Complex.I := by
      have h1 : ((x : ℂ) : ℂ) = (x : ℝ) • (1 : ℂ) := by
        simp [Complex.real_smul]
      have h2 : ((y : ℂ) * Complex.I) = (y : ℝ) • Complex.I := by
        simp [Complex.real_smul]
      rw [h1, h2, map_add, map_smul, map_smul]
    rw [hx, DZ, DZbar]
    simp only [Complex.real_smul, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_one]
    linear_combination ((y : ℂ) * fderiv ℝ H w Complex.I) * Complex.I_sq
  have hcomp : HasFDerivAt (fun z => F (G z))
      ((fderiv ℝ F (G ξ)).comp (fderiv ℝ G ξ)) ξ :=
    hF.hasFDerivAt.comp ξ hG.hasFDerivAt
  have hd : ∀ v : ℂ, fderiv ℝ (fun z => F (G z)) ξ v
      = fderiv ℝ F (G ξ) (fderiv ℝ G ξ v) := by
    intro v
    rw [hcomp.fderiv]
    rfl
  have e1 : fderiv ℝ (fun z => F (G z)) ξ 1
      = DZ F (G ξ) * (DZ G ξ + DZbar G ξ)
        + DZbar F (G ξ) * (starRingEnd ℂ (DZ G ξ) + starRingEnd ℂ (DZbar G ξ)) := by
    rw [hd 1, hdecomp G ξ 1, hdecomp F (G ξ)]
    simp only [map_one, map_add, map_mul]
    ring
  -- `Complex.conj_I` has already removed every `I^2` here, so this closes by
  -- plain `ring`; feeding it `Complex.I_sq` reintroduces `I^2` and it fails.
  have e2 : fderiv ℝ (fun z => F (G z)) ξ Complex.I
      = Complex.I * (DZ F (G ξ) * (DZ G ξ - DZbar G ξ)
          - DZbar F (G ξ) * (starRingEnd ℂ (DZ G ξ) - starRingEnd ℂ (DZbar G ξ))) := by
    rw [hd Complex.I, hdecomp G ξ Complex.I, hdecomp F (G ξ)]
    simp only [Complex.conj_I, map_add, map_mul, map_neg]
    ring
  refine ⟨?_, ?_⟩
  · rw [DZ, e1, e2]
    linear_combination (- (DZ F (G ξ) * (DZ G ξ - DZbar G ξ))
      + DZbar F (G ξ) * (starRingEnd ℂ (DZ G ξ) - starRingEnd ℂ (DZbar G ξ)))
      * Complex.I_sq / 2
  · rw [DZbar, e1, e2]
    linear_combination (DZ F (G ξ) * (DZ G ξ - DZbar G ξ)
      - DZbar F (G ξ) * (starRingEnd ℂ (DZ G ξ) - starRingEnd ℂ (DZbar G ξ)))
      * Complex.I_sq / 2
