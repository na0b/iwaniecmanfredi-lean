import IwaniecManfredi.Preamble
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory

/-- Bootstrapping for a first-order linear system: a pair of functions on an
open interval that are indefinite integrals of locally integrable functions
`U`, `V` and satisfy `(U, V) = M (u, v)` almost everywhere, with `M` of class
`C^∞`, are themselves `C^∞`.  No existence theory is involved and no
nondegeneracy of `M` is required -- a row may decouple.

This is what regains the paper's (31) once the coefficients satisfy the system
(33): `paper.tex:265-266` obtains `a_k ∈ C^∞(0,1)` from the standing assumption
that `H` is `C^∞` off the origin, and the content of this node is that the
one-dimensional system the coefficients satisfy delivers the same conclusion
from `W^{1,2}` data alone.  The hinge is that `u'` agrees almost everywhere
with a *continuous* function, so the indefinite integral is `C^1` with
derivative equal to it at every point, after which each differentiation of the
system raises the class by one. -/
theorem LinearOdeSystemSmooth (a b : ℝ) (hab : a < b) (u v U V : ℝ → ℂ)
    (M : Fin 2 → Fin 2 → (ℝ → ℂ))
    (hM : ∀ i j : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (M i j) (Set.Ioo a b))
    (hU : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, IntegrableOn U (Set.uIcc c d) volume)
    (hV : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, IntegrableOn V (Set.uIcc c d) volume)
    (hu : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, u d - u c = ∫ s in c..d, U s)
    (hv : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, v d - v c = ∫ s in c..d, V s)
    (hsys : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b →
      U r = M 0 0 r * u r + M 0 1 r * v r ∧ V r = M 1 0 r * u r + M 1 1 r * v r) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo a b) ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Set.Ioo a b) := by
  -- `I = Ioo a b` is order-connected, so the closed interval spanned by two of
  -- its points stays inside it.
  have hsub : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, Set.uIcc c d ⊆ Set.Ioo a b :=
    fun c hc d hd => Set.ordConnected_Ioo.uIcc_subset hc hd
  -- Every point of `I` has a left and a right neighbour inside `I`.
  have hleft : ∀ r ∈ Set.Ioo a b, (a + r) / 2 ∈ Set.Ioo a b ∧ (a + r) / 2 < r := by
    intro r hr
    obtain ⟨h1, h2⟩ := hr
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have hright : ∀ r ∈ Set.Ioo a b, (r + b) / 2 ∈ Set.Ioo a b ∧ r < (r + b) / 2 := by
    intro r hr
    obtain ⟨h1, h2⟩ := hr
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  -- Step 1: an indefinite integral of a locally integrable function is
  -- continuous on `I`.  Stated once and used for both `(u, U)` and `(v, V)`.
  have hcont : ∀ w F : ℝ → ℂ,
      (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, IntegrableOn F (Set.uIcc c d) volume) →
      (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, w d - w c = ∫ s in c..d, F s) →
      ContinuousOn w (Set.Ioo a b) := by
    intro w F hint hprim r hr
    obtain ⟨hc₁I, hc₁r⟩ := hleft r hr
    obtain ⟨hd₁I, hrd₁⟩ := hright r hr
    set c₁ := (a + r) / 2 with hc₁def
    set d₁ := (r + b) / 2 with hd₁def
    have hle : c₁ ≤ d₁ := by linarith
    have hintc : IntegrableOn F (Set.uIcc c₁ d₁) volume := hint c₁ hc₁I d₁ hd₁I
    have hprimcont : ContinuousOn (fun x => w c₁ + ∫ t in c₁..x, F t) (Set.uIcc c₁ d₁) :=
      continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval hintc)
    have hEq : ∀ x ∈ Set.uIcc c₁ d₁, w x = w c₁ + ∫ t in c₁..x, F t := by
      intro x hx
      have h := hprim c₁ hc₁I x (hsub c₁ hc₁I d₁ hd₁I hx)
      linear_combination h
    have hc := hprimcont.congr hEq
    have hnhds : Set.uIcc c₁ d₁ ∈ nhds r := by
      rw [Set.uIcc_of_le hle]
      exact Icc_mem_nhds hc₁r hrd₁
    exact (hc.continuousAt hnhds).continuousWithinAt
  have hcu : ContinuousOn u (Set.Ioo a b) := hcont u U hU hu
  have hcv : ContinuousOn v (Set.Ioo a b) := hcont v V hV hv
  -- Step 2 (the hinge): if the integrand agrees almost everywhere on `I` with a
  -- function `G` continuous on `I`, then `w` has derivative `G r` at *every*
  -- `r ∈ I`, not merely almost everywhere.
  have hderiv : ∀ w F G : ℝ → ℂ,
      (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, IntegrableOn F (Set.uIcc c d) volume) →
      (∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, w d - w c = ∫ s in c..d, F s) →
      ContinuousOn G (Set.Ioo a b) →
      (∀ᵐ r : ℝ, r ∈ Set.Ioo a b → F r = G r) →
      ∀ r ∈ Set.Ioo a b, HasDerivAt w (G r) r := by
    intro w F G hint hprim hG hae r hr
    -- Transport the primitive identity from `F` to `G`.
    have hprimG : ∀ c ∈ Set.Ioo a b, ∀ d ∈ Set.Ioo a b, w d - w c = ∫ s in c..d, G s := by
      intro c hc d hd
      rw [hprim c hc d hd]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hxmem
      exact hx (hsub c hc d hd (Set.uIoc_subset_uIcc hxmem))
    obtain ⟨hc₁I, hc₁r⟩ := hleft r hr
    set c₁ := (a + r) / 2 with hc₁def
    have hGint : IntervalIntegrable G volume c₁ r :=
      (hG.mono (hsub c₁ hc₁I r hr)).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter G (nhds r) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hG r hr
    have hGat : ContinuousAt G r := hG.continuousAt (isOpen_Ioo.mem_nhds hr)
    have hFTC : HasDerivAt (fun t => ∫ s in c₁..t, G s) (G r) r :=
      intervalIntegral.integral_hasDerivAt_right hGint hmeas hGat
    have hFTC2 : HasDerivAt (fun t => w c₁ + ∫ s in c₁..t, G s) (G r) r := hFTC.const_add _
    refine hFTC2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    have h := hprimG c₁ hc₁I t ht
    linear_combination h
  -- The two rows of the system, almost everywhere on `I`.
  have haeU : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b → U r = M 0 0 r * u r + M 0 1 r * v r := by
    filter_upwards [hsys] with r hr hrmem
    exact (hr hrmem).1
  have haeV : ∀ᵐ r : ℝ, r ∈ Set.Ioo a b → V r = M 1 0 r * u r + M 1 1 r * v r := by
    filter_upwards [hsys] with r hr hrmem
    exact (hr hrmem).2
  have hMc : ∀ i j : Fin 2, ContinuousOn (M i j) (Set.Ioo a b) := fun i j => (hM i j).continuousOn
  have hWc : ContinuousOn (fun r => M 0 0 r * u r + M 0 1 r * v r) (Set.Ioo a b) :=
    ((hMc 0 0).mul hcu).add ((hMc 0 1).mul hcv)
  have hZc : ContinuousOn (fun r => M 1 0 r * u r + M 1 1 r * v r) (Set.Ioo a b) :=
    ((hMc 1 0).mul hcu).add ((hMc 1 1).mul hcv)
  have hdu : ∀ r ∈ Set.Ioo a b, HasDerivAt u (M 0 0 r * u r + M 0 1 r * v r) r :=
    hderiv u U _ hU hu hWc haeU
  have hdv : ∀ r ∈ Set.Ioo a b, HasDerivAt v (M 1 0 r * u r + M 1 1 r * v r) r :=
    hderiv v V _ hV hv hZc haeV
  -- Step 3: simultaneous induction on the order of differentiability.
  have key : ∀ m : ℕ, ContDiffOn ℝ m u (Set.Ioo a b) ∧ ContDiffOn ℝ m v (Set.Ioo a b) := by
    intro m
    induction m with
    | zero => exact ⟨contDiffOn_zero.mpr hcu, contDiffOn_zero.mpr hcv⟩
    | succ k ih =>
      have hMk : ∀ i j : Fin 2, ContDiffOn ℝ k (M i j) (Set.Ioo a b) :=
        fun i j => contDiffOn_infty.mp (hM i j) k
      have hWk : ContDiffOn ℝ k (fun r => M 0 0 r * u r + M 0 1 r * v r) (Set.Ioo a b) :=
        ((hMk 0 0).mul ih.1).add ((hMk 0 1).mul ih.2)
      have hZk : ContDiffOn ℝ k (fun r => M 1 0 r * u r + M 1 1 r * v r) (Set.Ioo a b) :=
        ((hMk 1 0).mul ih.1).add ((hMk 1 1).mul ih.2)
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨fun r hr => (hdu r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
        · intro hk; simp at hk
        · exact hWk.congr fun r hr => (hdu r hr).deriv
      · rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨fun r hr => (hdv r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
        · intro hk; simp at hk
        · exact hZk.congr fun r hr => (hdv r hr).deriv
  exact ⟨contDiffOn_infty.mpr fun m => (key m).1, contDiffOn_infty.mpr fun m => (key m).2⟩
