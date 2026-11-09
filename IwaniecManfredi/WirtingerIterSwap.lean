import IwaniecManfredi.WirtingerIter
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-- On an open set where `H` is `C^∞`, every iterated Wirtinger derivative of
`H` is again `C^∞` there, and applying `∂/∂ξ̄` to `∂^{i+j}H/∂ξ^i ∂ξ̄^j` raises
the `ξ̄`-order: it gives `∂^{i+j+1}H/∂ξ^i ∂ξ̄^{j+1}`.  This is the commutation
of the two Wirtinger operators, which is what makes the order of application
in `WirtingerIter` immaterial. -/
theorem WirtingerIterSwap (H : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) (i j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (WirtingerIter i j H) Ω ∧
      ∀ ξ ∈ Ω, DZbar (WirtingerIter i j H) ξ = WirtingerIter i (j + 1) H ξ := by
  -- two functions agreeing on the open set Ω have the same ∂/∂ξ there
  have hdz_congr : ∀ (f₁ f₂ : ℂ → ℂ) (ξ : ℂ), ξ ∈ Ω → (∀ ζ ∈ Ω, f₁ ζ = f₂ ζ) →
      DZ f₁ ξ = DZ f₂ ξ := by
    intro f₁ f₂ ξ hξ h
    have hev : f₁ =ᶠ[nhds ξ] f₂ := by
      filter_upwards [hΩ.mem_nhds hξ] with ζ hζ using h ζ hζ
    rw [DZ, DZ, hev.fderiv_eq]
  -- STEP 1: both operators preserve C^∞(Ω)
  have hdz_cd : ∀ g : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g Ω →
      ContDiffOn ℝ (⊤ : ℕ∞) (DZ g) Ω := by
    intro g hg
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z) Ω :=
      hg.fderiv_of_isOpen hΩ (by simp)
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z 1) Ω :=
      hfd.clm_apply contDiffOn_const
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z Complex.I) Ω :=
      hfd.clm_apply contDiffOn_const
    have hrw : DZ g
        = fun z => (1 / 2 : ℂ) * (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) := rfl
    rw [hrw]
    exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul h2))
  have hdzbar_cd : ∀ g : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g Ω →
      ContDiffOn ℝ (⊤ : ℕ∞) (DZbar g) Ω := by
    intro g hg
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z) Ω :=
      hg.fderiv_of_isOpen hΩ (by simp)
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z 1) Ω :=
      hfd.clm_apply contDiffOn_const
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z Complex.I) Ω :=
      hfd.clm_apply contDiffOn_const
    have hrw : DZbar g
        = fun z => (1 / 2 : ℂ) * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) := rfl
    rw [hrw]
    exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul h2))
  -- STEP 3: the two operators commute on C^∞(Ω).  Schwarz enters here.
  have hcomm : ∀ g : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g Ω → ∀ ξ ∈ Ω,
      DZbar (DZ g) ξ = DZ (DZbar g) ξ := by
    intro g hg ξ hξ
    have hgat : ContDiffAt ℝ (⊤ : ℕ∞) g ξ := hg.contDiffAt (hΩ.mem_nhds hξ)
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z) Ω :=
      hg.fderiv_of_isOpen hΩ (by simp)
    have hfdd : DifferentiableAt ℝ (fun z => fderiv ℝ g z) ξ :=
      ((hfd.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ))
    have hA : ∀ v : ℂ, HasFDerivAt (fun z => fderiv ℝ g z v)
        ((fderiv ℝ (fderiv ℝ g) ξ).flip v) ξ := by
      intro v
      simpa using hfdd.hasFDerivAt.clm_apply (hasFDerivAt_const v ξ)
    have hDZ : ∀ w : ℂ, fderiv ℝ (DZ g) ξ w
        = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ g) ξ w 1
            - Complex.I * fderiv ℝ (fderiv ℝ g) ξ w Complex.I) := by
      intro w
      have hhas : HasFDerivAt
          (fun z => (1 / 2 : ℂ) * (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I))
          ((1 / 2 : ℂ) • ((fderiv ℝ (fderiv ℝ g) ξ).flip 1
            - Complex.I • (fderiv ℝ (fderiv ℝ g) ξ).flip Complex.I)) ξ :=
        ((hA 1).sub ((hA Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
      have hfe : fderiv ℝ (DZ g) ξ
          = fderiv ℝ (fun z => (1 / 2 : ℂ)
              * (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I)) ξ := rfl
      rw [hfe, hhas.fderiv]
      simp [smul_eq_mul]
    have hDZbar : ∀ w : ℂ, fderiv ℝ (DZbar g) ξ w
        = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ g) ξ w 1
            + Complex.I * fderiv ℝ (fderiv ℝ g) ξ w Complex.I) := by
      intro w
      have hhas : HasFDerivAt
          (fun z => (1 / 2 : ℂ) * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I))
          ((1 / 2 : ℂ) • ((fderiv ℝ (fderiv ℝ g) ξ).flip 1
            + Complex.I • (fderiv ℝ (fderiv ℝ g) ξ).flip Complex.I)) ξ :=
        ((hA 1).add ((hA Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
      have hfe : fderiv ℝ (DZbar g) ξ
          = fderiv ℝ (fun z => (1 / 2 : ℂ)
              * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)) ξ := rfl
      rw [hfe, hhas.fderiv]
      simp [smul_eq_mul]
      all_goals ring
    have hsymm : ∀ v w : ℂ, fderiv ℝ (fderiv ℝ g) ξ v w = fderiv ℝ (fderiv ℝ g) ξ w v :=
      hgat.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        norm_cast)
    rw [DZbar, DZ, hDZ 1, hDZ Complex.I, hDZbar 1, hDZbar Complex.I, hsymm Complex.I 1]
    ring
  -- (a), by induction
  have hiter : ∀ a b : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (WirtingerIter a b H) Ω := by
    have hbar : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (DZbar^[m] H) Ω := by
      intro m
      induction m with
      | zero => simpa using hH
      | succ c ih =>
          rw [Function.iterate_succ_apply']
          exact hdzbar_cd _ ih
    intro a b
    rw [WirtingerIter]
    induction a with
    | zero => simpa using hbar b
    | succ c ih =>
        rw [Function.iterate_succ_apply']
        exact hdz_cd _ ih
  refine ⟨hiter i j, ?_⟩
  -- (b), by induction on i with j fixed
  induction i with
  | zero =>
      intro ξ _
      show DZbar (DZ^[0] (DZbar^[j] H)) ξ = DZ^[0] (DZbar^[j + 1] H) ξ
      simp [Function.iterate_succ_apply']
  | succ c ih =>
      intro ξ hξ
      have e1 : WirtingerIter (c + 1) j H = DZ (WirtingerIter c j H) := by
        rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
      have e2 : WirtingerIter (c + 1) (j + 1) H = DZ (WirtingerIter c (j + 1) H) := by
        rw [WirtingerIter, WirtingerIter, Function.iterate_succ_apply']
      rw [e1, e2, hcomm _ (hiter c j) ξ hξ]
      exact hdz_congr _ _ ξ hξ (fun ζ hζ => ih ζ hζ)
