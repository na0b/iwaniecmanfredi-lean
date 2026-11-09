import IwaniecManfredi.DZ
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import IwaniecManfredi.DZbar
import IwaniecManfredi.ExtremalPolarForm
import IwaniecManfredi.ExtremalEpsBound
import IwaniecManfredi.ExtremalH
import IwaniecManfredi.VanishingDerivsIsPolynomial
import IwaniecManfredi.HomogPolyModFour
import IwaniecManfredi.WeakPartialEqFDerivAE
import IwaniecManfredi.MemHolderSmallOn
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.KAlphaExp
import IwaniecManfredi.KAlphaEqDExpAddOne

/-- Equation (56) of the paper, the heart of the optimality half of Theorem 1:
the inverse `f` of the extremal map (54) lies in neither
`C^{k-1+α}_loc` nor `W^{k+1,q}_loc` at the endpoint exponent
`q = 2/(2-α)`.

Two points of the statement are forced.  First, the two non-memberships are
asserted on an *arbitrary* open set `U` containing the singular point, not on
`ℂ`: non-membership is witnessed by a compact set on which the little-o or the
integral fails, and such a witness in `ℂ` need not meet a prescribed
subdomain, so a claim about `ℂ` does not restrict.  Second, the Sobolev
exponent is the endpoint `2/(2-α)` and nothing smaller: `(2-α)q = 2` is what
makes the Jacobian factor cancel in the scaling identity (59), and for
`q < 2/(2-α)` the conclusion is false -- that is why the positive half (10) of
Theorem 1 is a strict inequality.

The `f`-side facts are taken as hypotheses, as they are in `Cor2`,
`Thm1DerivBounds` and `ChiHigherDerivBound`; `ExtremalInverseGradient`
discharges them.  Here `k ≥ 1`, so `k - 1` is the ordinary predecessor. -/
theorem Section7Heart (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α ≤ 1) (hka : (k : ℝ) + α = KAlphaExp p)
    (U : Set ℂ) (hU : IsOpen U) (hU0 : (0 : ℂ) ∈ U)
    (f : ℂ → ℂ)
    (hfsm : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : ℂ)}ᶜ))
    (hfH : ∀ ξ : ℂ, f (ExtremalH p ξ) = ξ)
    (hHf : ∀ z : ℂ, ExtremalH p (f z) = z)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
      f ((t : ℂ) * z) = ((t ^ DExp p : ℝ) : ℂ) * f z)
    (hhomD : ∀ (w : List (Fin 2)) (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
      PartialWord w f ((t : ℂ) * z)
        = ((t ^ (DExp p - (w.length : ℝ)) : ℝ) : ℂ) * PartialWord w f z) :
    ¬ MemHolderSmallOn (k - 1) α U f ∧
      ¬ MemWLocOn (k + 1) (ENNReal.ofReal (2 / (2 - α))) U f := by
  -- ## Step 0: elementary consequences of the hypotheses
  -- (0a) `d = k - 1 + α`
  have h0a : DExp p = (k : ℝ) + α - 1 := by
    have h := KAlphaEqDExpAddOne p hp
    rw [h] at hka
    linarith
  -- (0b) `d > 0`
  have h0b : 0 < DExp p := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [h0a]
    linarith
  -- (0c) `f 0 = 0`
  have h0c : f 0 = 0 := by
    have h := hhom 0 le_rfl 1
    rw [Real.zero_rpow h0b.ne'] at h
    simpa using h
  -- (0d) `f` is not identically zero
  have h0d : f (ExtremalH p 1) = 1 := hfH 1
  -- (0g) if `α < 1` then `d - j ≠ 0` for every natural `j`
  have h0g : α < 1 → ∀ j : ℕ, DExp p - (j : ℝ) ≠ 0 := by
    intro hα1' j
    by_cases hj : j < k
    · have hjk : (j : ℝ) ≤ (k : ℝ) - 1 := by
        have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
        linarith
      rw [h0a]
      intro hcon
      have : (k : ℝ) - 1 + α - (j : ℝ) = 0 := by linarith
      linarith
    · have hjk : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.le_of_not_lt hj
      rw [h0a]
      intro hcon
      linarith
  -- ## Step 1: the standard facts
  -- every iterated partial of a `C^∞` function on an OPEN set is `C^∞` there
  have hPWcd : ∀ (w : List (Fin 2)) (g : ℂ → ℂ) (V : Set ℂ), IsOpen V →
      ContDiffOn ℝ (⊤ : ℕ∞) g V → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w g) V := by
    intro w
    induction w with
    | nil => intro g V _ hg; exact hg
    | cons j w ih =>
        intro g V hV hg
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w g) V := ih g V hV hg
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w g)) V :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hV).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  have hPWsm : ∀ w : List (Fin 2), ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) ({(0 : ℂ)}ᶜ) :=
    fun w => hPWcd w f _ isOpen_compl_singleton hfsm
  have hdiffat : ∀ (w : List (Fin 2)) (z : ℂ), z ≠ 0 → DifferentiableAt ℝ (PartialWord w f) z :=
    fun w z hz => ((hPWsm w).differentiableOn (by norm_num)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hz))
  -- (1a) the Wirtinger form of a real differential; no differentiability needed
  have hwform : ∀ (F : ℂ → ℂ) (u h : ℂ),
      fderiv ℝ F u h = DZ F u * h + DZbar F u * starRingEnd ℂ h := by
    intro F u h
    have hh : h = (h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hh]
    have h1 : fderiv ℝ F u ((h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I)
        = h.re • fderiv ℝ F u 1 + h.im • fderiv ℝ F u Complex.I := by
      rw [show ((h.re : ℂ) * 1 + (h.im : ℂ) * Complex.I)
          = h.re • (1 : ℂ) + h.im • Complex.I by simp [Complex.real_smul]]
      rw [map_add, map_smul, map_smul]
    rw [h1, DZ, DZbar]
    simp only [Complex.real_smul]
    apply Complex.ext <;> simp <;> ring
  -- the Euler identity at each word level, from (H4)
  have heulerW : ∀ (ν : List (Fin 2)) (z : ℂ), z ≠ 0 →
      z * DZ (PartialWord ν f) z + starRingEnd ℂ z * DZbar (PartialWord ν f) z
        = ((DExp p - (ν.length : ℝ) : ℝ) : ℂ) * PartialWord ν f z := by
    intro ν z hz
    obtain ⟨g, hgdef⟩ : ∃ u : ℂ → ℂ, u = PartialWord ν f := ⟨_, rfl⟩
    obtain ⟨m, hmdef⟩ : ∃ y : ℝ, y = DExp p - (ν.length : ℝ) := ⟨_, rfl⟩
    have hgd : DifferentiableAt ℝ g z := by rw [hgdef]; exact hdiffat ν z hz
    have hghom : ∀ t : ℝ, 0 < t → g ((t : ℂ) * z) = ((t ^ m : ℝ) : ℂ) * g z := by
      intro t ht
      rw [hgdef, hmdef]
      exact hhomD ν t ht z hz
    have hline : HasDerivAt (fun t : ℝ => ((t : ℂ) * z)) z 1 := by
      have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 1 := Complex.ofRealCLM.hasDerivAt
      simpa using h1.mul_const z
    have hpt : ((1 : ℝ) : ℂ) * z = z := by push_cast; ring
    have h2 : HasFDerivAt g (fderiv ℝ g z) (((1 : ℝ) : ℂ) * z) := by
      rw [hpt]; exact hgd.hasFDerivAt
    have hA : HasDerivAt (fun t : ℝ => g ((t : ℂ) * z)) (fderiv ℝ g z z) 1 :=
      h2.comp_hasDerivAt 1 hline
    have hrp : HasDerivAt (fun t : ℝ => t ^ m) m 1 := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ m) (m * (1 : ℝ) ^ (m - 1)) 1 :=
        Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
      rw [Real.one_rpow, mul_one] at h1
      exact h1
    have hrpC : HasDerivAt (fun t : ℝ => ((t ^ m : ℝ) : ℂ)) ((m : ℝ) : ℂ) 1 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 hrp
    have hB : HasDerivAt (fun t : ℝ => g ((t : ℂ) * z)) (((m : ℝ) : ℂ) * g z) 1 := by
      refine (hrpC.mul_const (g z)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
      exact hghom t ht
    have huniq := hA.unique hB
    rw [hwform g z z] at huniq
    rw [← hgdef, ← hmdef]
    linear_combination huniq
  -- a polynomial function of a real parameter vanishing on `(0,1)` has zero coefficients
  have hpolyzero : ∀ (N : ℕ) (c : ℕ → ℂ),
      (∀ s : ℝ, 0 < s → s < 1 → ∑ n ∈ Finset.range N, c n * ((s : ℂ)) ^ n = 0) →
      ∀ n, n < N → c n = 0 := by
    intro N c hvan n hn
    obtain ⟨P, hPdef⟩ : ∃ q : Polynomial ℂ,
        q = ∑ i ∈ Finset.range N, Polynomial.C (c i) * Polynomial.X ^ i := ⟨_, rfl⟩
    have hsub : (fun s : ℝ => ((s : ℝ) : ℂ)) '' Set.Ioo (0 : ℝ) 1 ⊆ {x | P.IsRoot x} := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hx
      show Polynomial.eval ((s : ℝ) : ℂ) P = 0
      rw [hPdef]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact hvan s hs.1 hs.2
    have hinf : {x : ℂ | P.IsRoot x}.Infinite := by
      refine Set.Infinite.mono hsub ?_
      refine Set.Infinite.image (Complex.ofReal_injective.injOn) ?_
      exact Set.Ioo_infinite (by norm_num)
    have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
    have hcoeff : P.coeff n = c n := by
      rw [hPdef, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hn)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
    rw [← hcoeff, hP0, Polynomial.coeff_zero]
  -- the unit circle is infinite, so a polynomial vanishing on it vanishes everywhere
  have hcircinf : (Metric.sphere (0 : ℂ) 1).Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => Complex.exp (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I)) ?_ ?_
    · intro n m hnm
      have hre := congrArg Complex.re hnm
      rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at hre
      have hpi : (1 : ℝ) < Real.pi := by linarith [Real.two_le_pi]
      have hmem : ∀ i : ℕ, (((i : ℝ) + 1)⁻¹ : ℝ) ∈ Set.Icc 0 Real.pi := by
        intro i
        have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
        refine ⟨by positivity, ?_⟩
        have h2 : (((i : ℝ) + 1)⁻¹ : ℝ) ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith
        linarith
      have heq := Real.injOn_cos (hmem n) (hmem m) hre
      have h1 : ((n : ℝ) + 1) = ((m : ℝ) + 1) := by
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        field_simp at heq
        linarith
      have : (n : ℝ) = (m : ℝ) := by linarith
      exact Nat.cast_injective this
    · intro n
      simp only [Metric.mem_sphere, dist_zero_right]
      exact Complex.norm_exp_ofReal_mul_I _
  have hpolycirc : ∀ P : Polynomial ℂ, (∀ ξ : ℂ, ‖ξ‖ = 1 → Polynomial.eval ξ P = 0) →
      ∀ ξ : ℂ, Polynomial.eval ξ P = 0 := by
    intro P hcirc
    have hsub : Metric.sphere (0 : ℂ) 1 ⊆ {x | P.IsRoot x} := by
      intro x hx
      simp only [Metric.mem_sphere, dist_zero_right] at hx
      exact hcirc x hx
    have hP0 : P = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot P (Set.Infinite.mono hsub hcircinf)
    intro ξ
    rw [hP0, Polynomial.eval_zero]
  -- (1c) the bridge from `PartialWord` to the iterated Fréchet derivative, at finite order
  have hbridge : ∀ (w : List (Fin 2)) (g : ℂ → ℂ) (V : Set ℂ), IsOpen V →
      ContDiffOn ℝ ((w.length : ℕ) : ℕ∞) g V → ∀ x ∈ V,
        PartialWord w g x
          = iteratedFDeriv ℝ w.length g x
              (fun i : Fin w.length => if w.get i = 0 then (1 : ℂ) else Complex.I) := by
    intro w
    induction w with
    | nil =>
        intro g V _ hg x hx
        simp [PartialWord, iteratedFDeriv_zero_apply]
    | cons j w ih =>
        intro g V hV hg x hx
        have hgw : ContDiffOn ℝ ((w.length : ℕ) : ℕ∞) g V := by
          refine hg.of_le ?_
          simp only [List.length_cons]
          exact_mod_cast Nat.le_succ _
        have hdiffn : DifferentiableOn ℝ (iteratedFDeriv ℝ w.length g) V := by
          have h1 : DifferentiableOn ℝ (iteratedFDerivWithin ℝ w.length g V) V := by
            refine hg.differentiableOn_iteratedFDerivWithin ?_ hV.uniqueDiffOn
            simp only [List.length_cons]
            exact_mod_cast Nat.lt_succ_self _
          exact h1.congr (fun y hy => (iteratedFDerivWithin_of_isOpen _ hV hy).symm)
        have hdat : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length g) x :=
          (hdiffn x hx).differentiableAt (hV.mem_nhds hx)
        set tv : Fin w.length → ℂ :=
          fun i => if w.get i = 0 then (1 : ℂ) else Complex.I with htv
        have hagree : ∀ y ∈ V, PartialWord w g y = iteratedFDeriv ℝ w.length g y tv :=
          fun y hy => ih g V hV hgw y hy
        have hfe : fderiv ℝ (PartialWord w g) x
            = fderiv ℝ (fun y => iteratedFDeriv ℝ w.length g y tv) x :=
          Filter.EventuallyEq.fderiv_eq
            (Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hagree)
        have hR : HasFDerivAt (fun y => iteratedFDeriv ℝ w.length g y tv)
            ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.length => ℂ) ℂ tv).comp
              (fderiv ℝ (iteratedFDeriv ℝ w.length g) x)) x :=
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.length => ℂ) ℂ tv).hasFDerivAt.comp x
            hdat.hasFDerivAt
        show fderiv ℝ (PartialWord w g) x (if j = 0 then (1 : ℂ) else Complex.I) = _
        rw [hfe, hR.fderiv]
        simp only [List.length_cons]
        rw [iteratedFDeriv_succ_apply_left]
        rfl
  -- the top partials of a `C^m` function are continuous on the open set
  have hPWcont : ∀ (m : ℕ) (ν : List (Fin 2)), ν.length = m → ContDiffOn ℝ ((m : ℕ) : ℕ∞) f U →
      ContinuousOn (PartialWord ν f) U := by
    intro m ν hν hCm
    subst hν
    have hb := hbridge ν f U hU hCm
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ ν.length f U) U :=
      hCm.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ ν.length f) U :=
      h1.congr (fun y hy => (iteratedFDerivWithin_of_isOpen _ hU hy).symm)
    have hev : ContinuousOn (fun x : ℂ => iteratedFDeriv ℝ ν.length f x
        (fun i : Fin ν.length => if ν.get i = 0 then (1 : ℂ) else Complex.I)) U :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin ν.length => ℂ) ℂ _).continuous.comp_continuousOn h2
    exact hev.congr (fun x hx => hb x hx)
  -- (3): the increment of a top partial is dominated by that of the full differential
  have hholder : ∀ (m : ℕ) (ν : List (Fin 2)), ν.length = m →
      ContDiffOn ℝ ((m : ℕ) : ℕ∞) f U → ∀ x ∈ U, ∀ y ∈ U,
        ‖PartialWord ν f x - PartialWord ν f y‖
          ≤ ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ := by
    intro m ν hν hCm x hx y hy
    subst hν
    rw [hbridge ν f U hU hCm x hx, hbridge ν f U hU hCm y hy]
    have h1 := (iteratedFDeriv ℝ ν.length f x - iteratedFDeriv ℝ ν.length f y).le_opNorm
      (fun i : Fin ν.length => if ν.get i = 0 then (1 : ℂ) else Complex.I)
    have hprod : ∏ i : Fin ν.length,
        ‖(if ν.get i = 0 then (1 : ℂ) else Complex.I)‖ = 1 := by
      refine Finset.prod_eq_one ?_
      intro i _
      split <;> simp
    rw [hprod, mul_one] at h1
    simpa using h1
  -- a function homogeneous of positive degree and continuous at `0` vanishes at `0`
  have hlim0 : ∀ (g : ℂ → ℂ) (β : ℝ), 0 < β → ContinuousAt g 0 →
      (∀ t : ℝ, 0 < t → ∀ z : ℂ, z ≠ 0 → g ((t : ℂ) * z) = ((t ^ β : ℝ) : ℂ) * g z) →
      g 0 = 0 := by
    intro g β hβ hcont hghom
    have hA : Filter.Tendsto (fun t : ℝ => g ((t : ℂ) * 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (g 0)) := by
      have h1 : Filter.Tendsto (fun t : ℝ => ((t : ℂ) * 1))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h2 : Filter.Tendsto (fun t : ℝ => ((t : ℂ) * 1)) (nhds (0 : ℝ))
            (nhds (((0 : ℝ) : ℂ) * 1)) :=
          (Complex.continuous_ofReal.mul continuous_const).tendsto 0
        simpa using h2.mono_left nhdsWithin_le_nhds
      exact hcont.tendsto.comp h1
    have hB : Filter.Tendsto (fun t : ℝ => g ((t : ℂ) * 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have heq : (fun t : ℝ => g ((t : ℂ) * 1))
          =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] (fun t : ℝ => ((t ^ β : ℝ) : ℂ) * g 1) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact hghom t ht 1 one_ne_zero
      refine Filter.Tendsto.congr' heq.symm ?_
      have h2 : Filter.Tendsto (fun t : ℝ => (t ^ β : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h3 := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
        rw [Real.zero_rpow hβ.ne'] at h3
        exact h3.mono_left nhdsWithin_le_nhds
      have h4 : Filter.Tendsto (fun t : ℝ => (((t ^ β : ℝ) : ℂ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h5 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h2
        rw [Complex.ofReal_zero] at h5
        exact h5
      simpa using h4.mul_const (g 1)
    exact tendsto_nhds_unique hA hB
  -- ## Step 2: the radial vanishing lemma, by downward induction on the word length
  have hstep2 : ∀ (m : ℕ) (z : ℂ), z ≠ 0 →
      (∀ j : ℕ, DExp p - (j : ℝ) ≠ 0) →
      (∀ ν : List (Fin 2), ν.length = m → PartialWord ν f z = 0) →
      f z = 0 := by
    intro m z hz hdj hvan
    have key : ∀ i : ℕ, ∀ ν : List (Fin 2), ν.length + i = m → PartialWord ν f z = 0 := by
      intro i
      induction i with
      | zero => intro ν hν; exact hvan ν (by omega)
      | succ i ih =>
          intro ν hν
          have h0 : PartialWord (0 :: ν) f z = 0 := by
            refine ih (0 :: ν) ?_
            simp only [List.length_cons]
            omega
          have h1 : PartialWord (1 :: ν) f z = 0 := by
            refine ih (1 :: ν) ?_
            simp only [List.length_cons]
            omega
          -- the downward step: both order-`(j+1)` partials vanish, so `D^ν f z = 0`
          have hDZ0 : DZ (PartialWord ν f) z = 0 := by
            show (1 / 2 : ℂ) * (fderiv ℝ (PartialWord ν f) z 1
              - Complex.I * fderiv ℝ (PartialWord ν f) z Complex.I) = 0
            have e0 : fderiv ℝ (PartialWord ν f) z 1 = 0 := by
              simpa [PartialWord, List.foldr] using h0
            have e1 : fderiv ℝ (PartialWord ν f) z Complex.I = 0 := by
              simpa [PartialWord, List.foldr] using h1
            rw [e0, e1]
            ring
          have hDZb0 : DZbar (PartialWord ν f) z = 0 := by
            show (1 / 2 : ℂ) * (fderiv ℝ (PartialWord ν f) z 1
              + Complex.I * fderiv ℝ (PartialWord ν f) z Complex.I) = 0
            have e0 : fderiv ℝ (PartialWord ν f) z 1 = 0 := by
              simpa [PartialWord, List.foldr] using h0
            have e1 : fderiv ℝ (PartialWord ν f) z Complex.I = 0 := by
              simpa [PartialWord, List.foldr] using h1
            rw [e0, e1]
            ring
          have hE := heulerW ν z hz
          rw [hDZ0, hDZb0] at hE
          have hc : ((DExp p - (ν.length : ℝ) : ℝ) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (hdj ν.length)
          have hzz : ((DExp p - (ν.length : ℝ) : ℝ) : ℂ) * PartialWord ν f z = 0 := by
            rw [← hE]; ring
          exact (mul_eq_zero.mp hzz).resolve_left hc
    have h := key m [] (by simp)
    simpa [PartialWord] using h
  -- ## Step 3: `f` cannot vanish on the whole unit circle
  have hstep3 : ∃ z₀ : ℂ, ‖z₀‖ = 1 ∧ f z₀ ≠ 0 := by
    by_contra hcon
    have hall : ∀ z₀ : ℂ, ‖z₀‖ = 1 → f z₀ = 0 := by
      intro z₀ h1
      by_contra h2
      exact hcon ⟨z₀, h1, h2⟩
    have hzero : ∀ z : ℂ, f z = 0 := by
      intro z
      rcases eq_or_ne z 0 with hz | hz
      · rw [hz]; exact h0c
      · have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
        have hnc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact hn.ne'
        have hu : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
          exact div_self hn.ne'
        have hzu : ((‖z‖ : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ)) = z := by field_simp
        have h := hhom ‖z‖ hn.le (z / ((‖z‖ : ℝ) : ℂ))
        rw [hzu, hall _ hu] at h
        simpa using h
    rw [hzero (ExtremalH p 1)] at h0d
    exact zero_ne_one h0d
  -- ## Step 4: the `α = 1` endgame
  have hstep4 : α = 1 → ∀ R : ℝ, 0 < R →
      (∀ ν : List (Fin 2), ν.length = k + 1 → ∀ z : ℂ, z ≠ 0 → ‖z‖ < R →
        PartialWord ν f z = 0) → False := by
    as_aux_lemma =>
      intro hα1' R hR hvanR
      have hdk : DExp p = (k : ℝ) := by rw [h0a, hα1']; ring
      -- (4) propagates from the punctured disc to the whole punctured plane, by (H4)
      have hvanall : ∀ ν : List (Fin 2), ν.length = k + 1 → ∀ z : ℂ, z ≠ 0 →
          PartialWord ν f z = 0 := by
        intro ν hν z hz
        have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
        have hnz : ‖z‖ ≠ 0 := hn.ne'
        obtain ⟨t, htdef⟩ : ∃ y : ℝ, y = R / (2 * ‖z‖) := ⟨_, rfl⟩
        have ht : 0 < t := by rw [htdef]; positivity
        have htc : ((t : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact ht.ne'
        have htzne : ((t : ℂ) * z) ≠ 0 := mul_ne_zero htc hz
        have htz : ‖(t : ℂ) * z‖ < R := by
          have h1 : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
          have h2 : t * ‖z‖ = R / 2 := by
            rw [htdef]
            field_simp
          rw [h1, h2]
          linarith
        have h := hhomD ν t ht z hz
        rw [hvanR ν hν _ htzne htz] at h
        have hc : ((t ^ (DExp p - (ν.length : ℝ)) : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact (Real.rpow_pos_of_pos ht _).ne'
        exact (mul_eq_zero.mp h.symm).resolve_left hc
      -- (4b) `f` is a polynomial of degree `≤ k` on the punctured plane
      obtain ⟨a, ha0, haf⟩ := VanishingDerivsIsPolynomial ({(0 : ℂ)}ᶜ) isOpen_compl_singleton
        (isConnected_compl_singleton_of_one_lt_rank
          (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) 0) k f hfsm
        (fun w hw z hz => hvanall w hw z (by simpa using hz))
      have hrep : ∀ w : ℂ, w ≠ 0 → f w = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          a i j * w ^ i * (starRingEnd ℂ w) ^ j := fun w hw => haf w (by simpa using hw)
      -- (4c), (4d): only the top-degree part survives
      have hQ : ∀ z : ℂ, z ≠ 0 →
          f z = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if i + j = k then a i j * z ^ i * (starRingEnd ℂ z) ^ j else 0) := by
        intro z hz
        obtain ⟨c, hcdef⟩ : ∃ u : ℕ → ℂ, u = fun n =>
            (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if i + j = n then a i j * z ^ i * (starRingEnd ℂ z) ^ j else 0))
              - (if n = k then f z else 0) := ⟨_, rfl⟩
        have hvan : ∀ s : ℝ, 0 < s → s < 1 →
            ∑ n ∈ Finset.range (2 * k + 1), c n * ((s : ℂ)) ^ n = 0 := by
          intro s hs0 hs1
          have hsc : ((s : ℝ) : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero]
            exact hs0.ne'
          have hsz : ((s : ℂ)) * z ≠ 0 := mul_ne_zero hsc hz
          have e1 : f ((s : ℂ) * z) = ((s ^ (k : ℕ) : ℝ) : ℂ) * f z := by
            have h := hhom s hs0.le z
            rw [hdk, Real.rpow_natCast] at h
            exact h
          have e2 : f ((s : ℂ) * z) = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              a i j * ((s : ℂ) * z) ^ i * (starRingEnd ℂ ((s : ℂ) * z)) ^ j := hrep _ hsz
          have e3 : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                a i j * ((s : ℂ) * z) ^ i * (starRingEnd ℂ ((s : ℂ) * z)) ^ j
              = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                a i j * z ^ i * (starRingEnd ℂ z) ^ j * ((s : ℂ)) ^ (i + j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [map_mul, Complex.conj_ofReal, mul_pow, mul_pow, pow_add]
            ring
          have hterm1 : (∑ n ∈ Finset.range (2 * k + 1),
                (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  (if i + j = n then a i j * z ^ i * (starRingEnd ℂ z) ^ j else 0)) * ((s : ℂ)) ^ n)
              = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  a i j * z ^ i * (starRingEnd ℂ z) ^ j * ((s : ℂ)) ^ (i + j) := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp only [Finset.mem_range] at hi hj
            rw [Finset.sum_eq_single_of_mem (i + j) (Finset.mem_range.mpr (by omega))
              (fun n _ hne => by simp [Ne.symm hne])]
            simp
          have hterm2 : (∑ n ∈ Finset.range (2 * k + 1), (if n = k then f z else 0) * ((s : ℂ)) ^ n)
              = f z * ((s : ℂ)) ^ k := by
            rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))
              (fun n _ hne => by simp [hne])]
            simp
          rw [hcdef]
          simp only [sub_mul]
          rw [Finset.sum_sub_distrib, hterm1, hterm2, ← e3, ← e2, e1]
          push_cast
          ring
        have h := hpolyzero (2 * k + 1) c hvan k (by omega)
        rw [hcdef] at h
        simp only [if_true] at h
        linear_combination -h
      -- reindex the top-degree part as a single sum over `m`
      have hQ' : ∀ z : ℂ, z ≠ 0 →
          f z = ∑ m ∈ Finset.range (k + 1), a m (k - m) * z ^ m * (starRingEnd ℂ z) ^ (k - m) := by
        intro z hz
        rw [hQ z hz]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [Finset.sum_eq_single_of_mem (k - i) (Finset.mem_range.mpr (by omega))
          (fun n _ hne => if_neg (by omega))]
        exact if_pos (by omega)
      -- `ε ≠ 0`, because `p ≠ 2`
      obtain ⟨ε, hεdef⟩ : ∃ y : ℝ, y = EpsCoef 1 2 p := ⟨_, rfl⟩
      have hεne : ((ε : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, hεdef]
        intro hc
        exact hp2 ((ExtremalEpsBound p hp).2.2.mp hc)
      -- (4e) the identity on the unit circle
      have hcircid : ∀ ξ : ℂ, ‖ξ‖ = 1 →
          ξ = ∑ m ∈ Finset.range (k + 1), a m (k - m)
                * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
                * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m) := by
        intro ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h
          rw [h] at hξ
          norm_num at hξ
        have hexp : Complex.exp ((ξ.arg : ℂ) * Complex.I) = ξ := by
          have h := Complex.norm_mul_exp_arg_mul_I ξ
          rw [hξ] at h
          simpa using h
        have hm3 : Complex.exp (-(3 * (ξ.arg : ℂ)) * Complex.I) = ξ ^ (-3 : ℤ) := by
          have h1 : -(3 * (ξ.arg : ℂ)) * Complex.I
              = ((-3 : ℤ) : ℂ) * ((ξ.arg : ℂ) * Complex.I) := by push_cast; ring
          rw [h1, Complex.exp_int_mul, hexp]
        have hpf := (ExtremalPolarForm p hp).1 1 one_pos ξ.arg
        rw [Real.one_rpow, hexp, hm3] at hpf
        have hH : ExtremalH p ξ = ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ) := by
          rw [hεdef]
          norm_num at hpf
          exact hpf
        have hmc : ξ * starRingEnd ℂ ξ = 1 := by
          rw [Complex.mul_conj, ← Complex.sq_norm, hξ]
          norm_num
        have hconjξ : starRingEnd ℂ ξ = ξ ^ (-1 : ℤ) := by
          rw [zpow_neg, zpow_one]
          field_simp
          linear_combination hmc
        have hconjH : starRingEnd ℂ (ExtremalH p ξ)
            = ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3 := by
          rw [hH, map_add, map_mul, Complex.conj_ofReal, hconjξ, map_zpow₀, hconjξ, ← zpow_mul]
          norm_num
        have hHne : ExtremalH p ξ ≠ 0 := by
          intro hc
          have h := hfH ξ
          rw [hc, h0c] at h
          rw [← h] at hξ
          norm_num at hξ
        have h := hfH ξ
        rw [hQ' (ExtremalH p ξ) hHne, hconjH, hH] at h
        exact h.symm
      -- the per-term identity behind (4f)
      have hterm : ∀ (ξ : ℂ), ξ ≠ 0 → ∀ m : ℕ, m ≤ k →
          ξ ^ (3 * k) * ((ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
              * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m))
            = ξ ^ (2 * (k - m)) * ((ξ ^ 4 + ((ε : ℝ) : ℂ)) ^ m
              * (1 + ((ε : ℝ) : ℂ) * ξ ^ 4) ^ (k - m)) := by
        intro ξ hξ m hm
        have g1 : (ξ ^ 3) * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) = ξ ^ 4 + ((ε : ℝ) : ℂ) := by
          rw [zpow_neg]
          field_simp
        have g2 : ξ * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) = 1 + ((ε : ℝ) : ℂ) * ξ ^ 4 := by
          rw [zpow_neg, zpow_one]
          field_simp
        have h1 : (ξ ^ 3) ^ m * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
            = (ξ ^ 4 + ((ε : ℝ) : ℂ)) ^ m := by
          rw [← mul_pow, g1]
        have h2 : ξ ^ (k - m) * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m)
            = (1 + ((ε : ℝ) : ℂ) * ξ ^ 4) ^ (k - m) := by
          rw [← mul_pow, g2]
        have harith : 3 * k = 3 * m + ((k - m) + 2 * (k - m)) := by omega
        have hx3 : ξ ^ (3 * k) = (ξ ^ 3) ^ m * ξ ^ (k - m) * ξ ^ (2 * (k - m)) := by
          rw [← pow_mul, harith, pow_add, pow_add]
          ring
        rw [hx3, ← h1, ← h2]
        ring
      -- (4f) the polynomial continuation
      obtain ⟨P, hPdef⟩ : ∃ q : Polynomial ℂ, q = Polynomial.X ^ (3 * k + 1)
          - ∑ m ∈ Finset.range (k + 1), Polynomial.C (a m (k - m)) * Polynomial.X ^ (2 * (k - m))
              * (Polynomial.X ^ 4 + Polynomial.C ((ε : ℝ) : ℂ)) ^ m
              * (1 + Polynomial.C ((ε : ℝ) : ℂ) * Polynomial.X ^ 4) ^ (k - m) := ⟨_, rfl⟩
      have hPev : ∀ ξ : ℂ, Polynomial.eval ξ P = ξ ^ (3 * k + 1)
          - ∑ m ∈ Finset.range (k + 1), a m (k - m) * ξ ^ (2 * (k - m))
              * (ξ ^ 4 + ((ε : ℝ) : ℂ)) ^ m * (1 + ((ε : ℝ) : ℂ) * ξ ^ 4) ^ (k - m) := by
        intro ξ
        rw [hPdef]
        simp [Polynomial.eval_finsetSum]
      have hPcirc : ∀ ξ : ℂ, ‖ξ‖ = 1 → Polynomial.eval ξ P = 0 := by
        intro ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h
          rw [h] at hξ
          norm_num at hξ
        rw [hPev]
        have hc := hcircid ξ hξ
        have hsum : ∑ m ∈ Finset.range (k + 1), a m (k - m) * ξ ^ (2 * (k - m))
              * (ξ ^ 4 + ((ε : ℝ) : ℂ)) ^ m * (1 + ((ε : ℝ) : ℂ) * ξ ^ 4) ^ (k - m)
            = ξ ^ (3 * k) * ∑ m ∈ Finset.range (k + 1), a m (k - m)
                * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
                * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro m hm
          simp only [Finset.mem_range] at hm
          have h := hterm ξ hξ0 m (by omega)
          linear_combination (-(a m (k - m))) * h
        rw [hsum, ← hc, pow_succ]
        ring
      have hPall := hpolycirc P hPcirc
      -- (9) at every `ξ ≠ 0`
      have h60 : ∀ ξ : ℂ, ξ ≠ 0 →
          ξ = ∑ m ∈ Finset.range (k + 1), a m (k - m) * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
                * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m) := by
        intro ξ hξ
        have h := hPall ξ
        rw [hPev] at h
        have hxne : ξ ^ (3 * k) ≠ 0 := pow_ne_zero _ hξ
        refine mul_left_cancel₀ hxne ?_
        have hsum : ξ ^ (3 * k) * ∑ m ∈ Finset.range (k + 1), a m (k - m)
                * (ξ + ((ε : ℝ) : ℂ) * ξ ^ (-3 : ℤ)) ^ m
                * (ξ ^ (-1 : ℤ) + ((ε : ℝ) : ℂ) * ξ ^ 3) ^ (k - m)
            = ∑ m ∈ Finset.range (k + 1), a m (k - m) * ξ ^ (2 * (k - m))
              * (ξ ^ 4 + ((ε : ℝ) : ℂ)) ^ m * (1 + ((ε : ℝ) : ℂ) * ξ ^ 4) ^ (k - m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro m hm
          simp only [Finset.mem_range] at hm
          have h2 := hterm ξ hξ m (by omega)
          linear_combination (a m (k - m)) * h2
        rw [hsum]
        have hpow : ξ ^ (3 * k + 1) = ξ ^ (3 * k) * ξ := pow_succ ξ (3 * k)
        rw [hpow] at h
        linear_combination h
      exact HomogPolyModFour ((ε : ℝ) : ℂ) hεne k hk a h60
  -- ## Steps 5 and 6: the two non-memberships
  have hstep5 : ¬ MemHolderSmallOn (k - 1) α U f := by
    as_aux_lemma =>
      intro hmem
      obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : ℂ) ρ ⊆ U := by
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU 0 hU0
        refine ⟨r / 2, by positivity, fun x hx => hrU ?_⟩
        refine Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) ?_)
        linarith
      obtain ⟨z₀, hz₀n, hz₀⟩ := hstep3
      have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have h1 : (1 : ℕ) ≤ k := hk
        rw [Nat.cast_sub h1]
        norm_num
      have hexpα : DExp p - ((k - 1 : ℕ) : ℝ) = α := by rw [h0a, hkm]; ring
      obtain ⟨w₀, hw₀def⟩ : ∃ y : ℂ, y = ((ρ : ℝ) : ℂ) * z₀ := ⟨_, rfl⟩
      have hw₀n : ‖w₀‖ = ρ := by
        rw [hw₀def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hz₀n, mul_one]
      have hw₀ne : w₀ ≠ 0 := by
        rw [← norm_pos_iff, hw₀n]
        exact hρ
      have hw₀U : w₀ ∈ U := hρU (by rw [Metric.mem_closedBall, dist_zero_right, hw₀n])
      -- the common endgame of Case A: all words of length `k-1` kill `f` at `w₀`
      have hfinal : α < 1 → (∀ ν : List (Fin 2), ν.length = k - 1 → PartialWord ν f w₀ = 0) →
          False := by
        intro hαlt hvan
        have hfw : f w₀ = 0 := hstep2 (k - 1) w₀ hw₀ne (h0g hαlt) hvan
        have h := hhom ρ hρ.le z₀
        rw [← hw₀def, hfw] at h
        have hc : ((ρ ^ DExp p : ℝ) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact (Real.rpow_pos_of_pos hρ _).ne'
        exact hz₀ ((mul_eq_zero.mp h.symm).resolve_left hc)
      rcases hmem with ⟨hα1', hCB⟩ | ⟨hαlt, hCA, hhold⟩
      · -- ## Case B: `α = 1`, so `f` is `C^k` on `U`
        have hCk1 : ContDiffOn ℝ (((k - 1 : ℕ) : ℕ) : ℕ∞) f U :=
          hCB.of_succ
        have hPWdiff : ∀ ν : List (Fin 2), ν.length = k - 1 →
            DifferentiableOn ℝ (PartialWord ν f) U := by
          intro ν hν
          have hb := hbridge ν f U hU (by rw [hν]; exact hCk1)
          have h1 : DifferentiableOn ℝ (iteratedFDerivWithin ℝ ν.length f U) U := by
            refine hCB.differentiableOn_iteratedFDerivWithin ?_ hU.uniqueDiffOn
            rw [hν]
            exact_mod_cast Nat.lt_succ_self _
          have h2 : DifferentiableOn ℝ (iteratedFDeriv ℝ ν.length f) U :=
            h1.congr (fun y hy => (iteratedFDerivWithin_of_isOpen _ hU hy).symm)
          intro x hx
          refine DifferentiableWithinAt.congr ?_ (fun y hy => hb y hy) (hb x hx)
          exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin ν.length => ℂ) ℂ
            (fun i : Fin ν.length => if ν.get i = 0 then (1 : ℂ) else Complex.I)).differentiableAt.comp_differentiableWithinAt x (h2 x hx)
        -- (13): each `(k-1)`-st partial is the restriction of its own differential at `0`
        have h13 : ∀ ν : List (Fin 2), ν.length = k - 1 → ∀ z : ℂ, z ≠ 0 →
            PartialWord ν f z = fderiv ℝ (PartialWord ν f) 0 z := by
          intro ν hν z hz
          obtain ⟨g, hgdef⟩ : ∃ u : ℂ → ℂ, u = PartialWord ν f := ⟨_, rfl⟩
          have hgd0 : DifferentiableAt ℝ g 0 := by
            rw [hgdef]
            exact ((hPWdiff ν hν) 0 hU0).differentiableAt (hU.mem_nhds hU0)
          have hgcont : ContinuousAt g 0 := by
            rw [hgdef]
            exact (hPWcont (k - 1) ν hν hCk1).continuousAt (hU.mem_nhds hU0)
          have hghom : ∀ t : ℝ, 0 < t → ∀ w : ℂ, w ≠ 0 →
              g ((t : ℂ) * w) = ((t ^ α : ℝ) : ℂ) * g w := by
            intro t ht w hw
            rw [hgdef, hhomD ν t ht w hw, hν, hexpα]
          have hg0 : g 0 = 0 := hlim0 g α hα hgcont hghom
          have hline : HasDerivAt (fun t : ℝ => ((t : ℂ) * z)) z 0 := by
            have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
            simpa using h1.mul_const z
          have hpt : ((0 : ℝ) : ℂ) * z = 0 := by push_cast; ring
          have h2 : HasFDerivAt g (fderiv ℝ g 0) (((0 : ℝ) : ℂ) * z) := by
            rw [hpt]
            exact hgd0.hasFDerivAt
          have hA : HasDerivAt (fun t : ℝ => g ((t : ℂ) * z)) (fderiv ℝ g 0 z) 0 :=
            h2.comp_hasDerivAt 0 hline
          have hB : HasDerivAt (fun t : ℝ => ((t : ℂ)) * g z) (g z) 0 := by
            have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
            simpa using h1.mul_const (g z)
          have hAw : HasDerivWithinAt (fun t : ℝ => g ((t : ℂ) * z)) (fderiv ℝ g 0 z)
            (Set.Ioi 0) 0 := hA.hasDerivWithinAt
          have hBw : HasDerivWithinAt (fun t : ℝ => g ((t : ℂ) * z)) (g z) (Set.Ioi 0) 0 := by
            refine (hB.hasDerivWithinAt).congr_of_eventuallyEq ?_ ?_
            · have heq : (fun t : ℝ => g ((t : ℂ) * z))
                  =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] (fun t : ℝ => ((t : ℂ)) * g z) := by
                filter_upwards [self_mem_nhdsWithin] with t ht
                rw [hghom t ht z hz, hα1', Real.rpow_one]
              exact heq
            · rw [hpt, hg0]
              push_cast
              ring
          have huniq := (uniqueDiffWithinAt_Ioi (0 : ℝ)).eq_deriv _ hAw hBw
          rw [hgdef] at huniq
          exact huniq.symm
        -- all partials of order `k+1` vanish off the origin
        have hvan2 : ∀ ν' : List (Fin 2), ν'.length = k + 1 → ∀ z : ℂ, z ≠ 0 →
            PartialWord ν' f z = 0 := by
          intro ν' hν' z hz
          rcases ν' with _ | ⟨j₁, ν''⟩
          · simp only [List.length_nil] at hν'
            omega
          · rcases ν'' with _ | ⟨j₂, ν⟩
            · simp only [List.length_cons, List.length_nil] at hν'
              omega
            · have hν : ν.length = k - 1 := by
                simp only [List.length_cons] at hν'
                omega
                -- `D^{j₂ :: ν} f` is constant off the origin
              have hconst : ∀ w : ℂ, w ≠ 0 →
                  PartialWord (j₂ :: ν) f w
                    = fderiv ℝ (PartialWord ν f) 0 (if j₂ = 0 then (1 : ℂ) else Complex.I) := by
                intro w hw
                show fderiv ℝ (PartialWord ν f) w (if j₂ = 0 then (1 : ℂ) else Complex.I) = _
                have heq : (PartialWord ν f)
                    =ᶠ[nhds w] (fun y : ℂ => fderiv ℝ (PartialWord ν f) 0 y) := by
                  filter_upwards [isOpen_compl_singleton.mem_nhds
                    (show w ∈ ({(0 : ℂ)}ᶜ : Set ℂ) by simpa using hw)] with y hy
                  exact h13 ν hν y (by simpa using hy)
                rw [Filter.EventuallyEq.fderiv_eq heq, (fderiv ℝ (PartialWord ν f) 0).fderiv]
              show fderiv ℝ (PartialWord (j₂ :: ν) f) z (if j₁ = 0 then (1 : ℂ) else Complex.I) = 0
              have heq2 : (PartialWord (j₂ :: ν) f)
                  =ᶠ[nhds z] (fun _ : ℂ =>
                    fderiv ℝ (PartialWord ν f) 0 (if j₂ = 0 then (1 : ℂ) else Complex.I)) := by
                filter_upwards [isOpen_compl_singleton.mem_nhds
                  (show z ∈ ({(0 : ℂ)}ᶜ : Set ℂ) by simpa using hz)] with y hy
                exact hconst y (by simpa using hy)
              rw [Filter.EventuallyEq.fderiv_eq heq2]
              simp
        exact hstep4 hα1' 1 one_pos (fun ν' hν' z hz _ => hvan2 ν' hν' z hz)
      · -- ## Case A: `α < 1`
        refine hfinal hαlt ?_
        intro ν hν
        obtain ⟨C, hCdef⟩ : ∃ y : ℂ, y = PartialWord ν f w₀ := ⟨_, rfl⟩
        have h2α : (0 : ℝ) < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
        have h2α1 : (2 : ℝ) ^ (-α) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
        have hρα : (0 : ℝ) < ρ ^ α := Real.rpow_pos_of_pos hρ _
        -- the two-point Hölder estimate, at `t w₀` and `(t/2) w₀`
        have hkey : ∀ δ : ℝ, 0 < δ →
            ‖C‖ * (1 - (2 : ℝ) ^ (-α)) ≤ δ * ((2 : ℝ) ^ (-α) * ρ ^ α) := by
          intro δ hδ
          obtain ⟨r, hr, hb⟩ := hhold (Metric.closedBall 0 ρ) hρU (isCompact_closedBall _ _) δ hδ
          obtain ⟨t, htdef⟩ : ∃ y : ℝ, y = min 1 (r / ρ) := ⟨_, rfl⟩
          have ht0 : 0 < t := by
            rw [htdef]
            exact lt_min one_pos (by positivity)
          have ht1 : t ≤ 1 := by
            rw [htdef]
            exact min_le_left _ _
          have htr : t * ρ ≤ r := by
            have h1 : t ≤ r / ρ := by
              rw [htdef]
              exact min_le_right _ _
            calc t * ρ ≤ (r / ρ) * ρ := by nlinarith
              _ = r := by field_simp
          obtain ⟨x, hxdef⟩ : ∃ y : ℂ, y = ((t : ℝ) : ℂ) * w₀ := ⟨_, rfl⟩
          obtain ⟨y, hydef⟩ : ∃ u : ℂ, u = (((t / 2 : ℝ)) : ℂ) * w₀ := ⟨_, rfl⟩
          have hxn : ‖x‖ = t * ρ := by
            rw [hxdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hw₀n]
          have hyn : ‖y‖ = (t / 2) * ρ := by
            rw [hydef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0 : ℝ) < t / 2), hw₀n]
          have hxK : x ∈ Metric.closedBall (0 : ℂ) ρ := by
            rw [Metric.mem_closedBall, dist_zero_right, hxn]
            nlinarith
          have hyK : y ∈ Metric.closedBall (0 : ℂ) ρ := by
            rw [Metric.mem_closedBall, dist_zero_right, hyn]
            nlinarith
          have hxy : x - y = (((t / 2 : ℝ)) : ℂ) * w₀ := by
            rw [hxdef, hydef]
            push_cast
            ring
          have hxyn : ‖x - y‖ = (t / 2) * ρ := by
            rw [hxy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0 : ℝ) < t / 2), hw₀n]
          have hlt : ‖x - y‖ < r := by
            rw [hxyn]
            nlinarith
          have hbd := hb x hxK y hyK hlt
          rw [iteratedFDerivWithin_of_isOpen _ hU (hρU hxK),
            iteratedFDerivWithin_of_isOpen _ hU (hρU hyK)] at hbd
          have hH := hholder (k - 1) ν hν hCA x (hρU hxK) y (hρU hyK)
          have hxv : PartialWord ν f x = ((t ^ α : ℝ) : ℂ) * C := by
            rw [hxdef, hhomD ν t ht0 w₀ hw₀ne, hν, hexpα, hCdef]
          have hyv : PartialWord ν f y = (((t / 2) ^ α : ℝ) : ℂ) * C := by
            rw [hydef, hhomD ν (t / 2) (by positivity) w₀ hw₀ne, hν, hexpα, hCdef]
          have htα : (0 : ℝ) < t ^ α := Real.rpow_pos_of_pos ht0 _
          have hhalf : ((t / 2) ^ α : ℝ) = t ^ α * (2 : ℝ) ^ (-α) := by
            rw [Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num)]
            ring
          have hnormdiff : ‖PartialWord ν f x - PartialWord ν f y‖
              = (t ^ α * (1 - (2 : ℝ) ^ (-α))) * ‖C‖ := by
            rw [hxv, hyv, hhalf,
              show ((t ^ α : ℝ) : ℂ) * C - ((t ^ α * (2 : ℝ) ^ (-α) : ℝ) : ℂ) * C
                = (((t ^ α * (1 - (2 : ℝ) ^ (-α))) : ℝ) : ℂ) * C by push_cast; ring,
              norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0 : ℝ) < t ^ α * (1 - (2 : ℝ) ^ (-α)))]
          have hrhs : δ * ‖x - y‖ ^ α = δ * (t ^ α * ((2 : ℝ) ^ (-α) * ρ ^ α)) := by
            rw [hxyn, Real.mul_rpow (by positivity) hρ.le, hhalf]
            ring
          rw [hnormdiff] at hH
          have hcomb : (t ^ α * (1 - (2 : ℝ) ^ (-α))) * ‖C‖
              ≤ δ * (t ^ α * ((2 : ℝ) ^ (-α) * ρ ^ α)) := by
            rw [← hrhs]
            exact le_trans hH hbd
          have hfin : t ^ α * (‖C‖ * (1 - (2 : ℝ) ^ (-α)))
              ≤ t ^ α * (δ * ((2 : ℝ) ^ (-α) * ρ ^ α)) := by nlinarith [hcomb]
          exact le_of_mul_le_mul_left hfin htα
        -- `δ` was arbitrary, so `C = 0`
        have hnorm : ‖C‖ = 0 := by
          by_contra hne
          have hCpos : 0 < ‖C‖ := lt_of_le_of_ne (norm_nonneg C) (Ne.symm hne)
          have hA : (0 : ℝ) < (2 : ℝ) ^ (-α) * ρ ^ α := by positivity
          have h := hkey (‖C‖ * (1 - (2 : ℝ) ^ (-α)) / (2 * ((2 : ℝ) ^ (-α) * ρ ^ α)))
            (by positivity)
          have hδA : (‖C‖ * (1 - (2 : ℝ) ^ (-α)) / (2 * ((2 : ℝ) ^ (-α) * ρ ^ α)))
                * ((2 : ℝ) ^ (-α) * ρ ^ α) = ‖C‖ * (1 - (2 : ℝ) ^ (-α)) / 2 := by
            field_simp
          rw [hδA] at h
          nlinarith [h, hCpos, h2α1]
        rw [← hCdef]
        exact norm_eq_zero.mp hnorm
  have hstep6 : ¬ MemWLocOn (k + 1) (ENNReal.ofReal (2 / (2 - α))) U f := by
    -- (0f): the endpoint exponent
    have h2α : (0 : ℝ) < 2 - α := by linarith
    obtain ⟨q, hqdef⟩ : ∃ y : ℝ, y = 2 / (2 - α) := ⟨_, rfl⟩
    have hq0 : 0 < q := by rw [hqdef]; positivity
    have hq1 : 1 ≤ q := by
      rw [hqdef, le_div_iff₀ h2α]
      linarith
    have hqq : (2 - α) * q = 2 := by
      rw [hqdef]
      field_simp
    rw [← hqdef]
    intro hmem
    obtain ⟨D, hD0, hDloc, hDweak⟩ := hmem
    -- the punctured domain `Ω' = U - {0}`
    have hΩopen : IsOpen (U \ {(0 : ℂ)}) := hU.sdiff isClosed_singleton
    have hΩsub : (U \ {(0 : ℂ)}) ⊆ U := Set.sdiff_subset
    have hΩne : ∀ z ∈ (U \ {(0 : ℂ)}), z ≠ 0 := fun z hz => by simpa using hz.2
    have hΩcpl : (U \ {(0 : ℂ)}) ⊆ ({(0 : ℂ)}ᶜ : Set ℂ) := fun z hz => by simpa using hz.2
    have hfsmΩ : ContDiffOn ℝ (⊤ : ℕ∞) f (U \ {(0 : ℂ)}) := hfsm.mono hΩcpl
    -- continuity gives local `L¹` on any set
    have hcontLpOn : ∀ (Ω : Set ℂ) (u : ℂ → ℂ), ContinuousOn u Ω → MemLpLocOn 1 Ω u := by
      intro Ω u hu K hKsub hK
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.mono hKsub)
      have hm : MeasureTheory.AEStronglyMeasurable (K.indicator u) MeasureTheory.volume := by
        rw [aestronglyMeasurable_indicator_iff hK.measurableSet]
        exact (hu.mono hKsub).aestronglyMeasurable hK.measurableSet
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
    -- each `D w` is locally `L¹` on `Ω'`, by Hölder on compact subsets (`q ≥ 1`)
    have hqE : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal hq1
    have hDL1 : ∀ w : List (Fin 2), w.length ≤ k + 1 →
        MemLpLocOn 1 (U \ {(0 : ℂ)}) (D w) := by
      intro w hw K hKsub hK
      refine MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top
        (hDloc w hw K (hKsub.trans hΩsub) hK) ?_ hK.measure_lt_top.ne hqE
      intro x hx
      exact Set.indicator_of_notMem hx _
    -- the composition law for `PartialWord`
    have happ : ∀ (w v : List (Fin 2)) (g : ℂ → ℂ),
        PartialWord w (PartialWord v g) = PartialWord (w ++ v) g := by
      intro w v g
      simp only [PartialWord, List.foldr_append]
    -- (6a) the identification of the weak derivatives, with the reversal carried
    have h6a : ∀ w : List (Fin 2), w.length ≤ k + 1 →
        ∀ᵐ z : ℂ, z ∈ (U \ {(0 : ℂ)}) → D w z = PartialWord w.reverse f z := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
          intro _
          filter_upwards with z _
          rw [hD0]
          rfl
      | append_singleton v j ih =>
          intro hlen
          have hvlen : v.length ≤ k + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen
            omega
          have hvlt : v.length < k + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen
            omega
          have hv := ih hvlen
          -- the two candidate weak derivatives of `u = D^{reverse v} f` on `Ω'`
          have hweak : ∀ i : Fin 2,
              IsWeakPartialOn (U \ {(0 : ℂ)}) i (PartialWord v.reverse f) (D (v ++ [i])) := by
            intro i φ hφ
            have hφU : IsTestFn U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hΩsub⟩
            have h := hDweak v i hvlt φ hφU
            rw [← h]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [hv] with z hz
            by_cases hzΩ : z ∈ (U \ {(0 : ℂ)})
            · rw [hz hzΩ]
            · have hd0 : fderiv ℝ φ z = 0 := by
                refine fderiv_of_notMem_tsupport ℝ ?_
                intro hc
                exact hzΩ (hφ.2.2 hc)
              rw [hd0]
              simp
          have hbr := WeakPartialEqFDerivAE (U \ {(0 : ℂ)}) hΩopen (PartialWord v.reverse f)
            (fun i => D (v ++ [i]))
            (hcontLpOn _ _ (hPWcd v.reverse f _ hΩopen hfsmΩ).continuousOn)
            (fun i => hDL1 (v ++ [i]) (by
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
              omega))
            hweak
            (Filter.Eventually.of_forall (fun z hz => hdiffat v.reverse z (hΩne z hz)))
          filter_upwards [hbr j] with z hz hzΩ
          rw [hz hzΩ, happ [j] v.reverse f, List.reverse_append]
          rfl
    -- two continuous functions on an open set agreeing a.e. agree everywhere
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
    -- a closed ball inside `U`
    obtain ⟨R, hR, hRU⟩ : ∃ R : ℝ, 0 < R ∧ Metric.closedBall (0 : ℂ) R ⊆ U := by
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU 0 hU0
      refine ⟨r / 2, by positivity, fun x hx => hrU ?_⟩
      refine Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) ?_)
      linarith
    -- (17): every partial of order `k+1` vanishes off the origin
    have h17 : ∀ ν : List (Fin 2), ν.length = k + 1 → ∀ z : ℂ, z ≠ 0 →
        PartialWord ν f z = 0 := by
      intro ν hν
      obtain ⟨F, hFdef⟩ : ∃ u : ℂ → ℂ, u = PartialWord ν f := ⟨_, rfl⟩
      obtain ⟨G, hGdef⟩ : ∃ u : ℂ → ℝ, u = fun z => ‖F z‖ ^ q := ⟨_, rfl⟩
      have hG0 : ∀ z : ℂ, 0 ≤ G z := by
        intro z
        rw [hGdef]
        positivity
      have hFcont : ContinuousOn F ({(0 : ℂ)}ᶜ) := by
        rw [hFdef]
        exact (hPWsm ν).continuousOn
      -- (16) the scaling of `F`, from (H4)
      have h16 : ∀ (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
          F ((t : ℂ) * z) = ((t ^ (α - 2) : ℝ) : ℂ) * F z := by
        intro t ht z hz
        rw [hFdef, hhomD ν t ht z hz, hν]
        congr 3
        rw [h0a]
        push_cast
        ring
      -- the induced scaling of `G = |F|^q`, where the endpoint exponent is used
      have hGscale : ∀ (t : ℝ), 0 < t → ∀ z : ℂ, z ≠ 0 →
          G ((t : ℝ) • z) = (t ^ 2)⁻¹ * G z := by
        intro t ht z hz
        have hsm : ((t : ℝ) • z) = ((t : ℂ) * z) := by rw [Complex.real_smul]
        have hexp : (t : ℝ) ^ ((α - 2) * q) = (t ^ 2)⁻¹ := by
          have h1 : (α - 2) * q = -(2 : ℝ) := by nlinarith [hqq]
          rw [h1, Real.rpow_neg ht.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [hGdef]
        simp only
        rw [hsm, h16 t ht z hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos ht _),
          Real.mul_rpow (Real.rpow_nonneg ht.le _) (norm_nonneg _), ← Real.rpow_mul ht.le, hexp]
      -- (6b) `G` is integrable on the ball
      have hball : Metric.ball (0 : ℂ) R ⊆ Metric.closedBall (0 : ℂ) R :=
        Metric.ball_subset_closedBall
      have hKcpt : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
      have hMLp := hDloc ν.reverse (by simp [hν]) (Metric.closedBall (0 : ℂ) R) hRU hKcpt
      have hInt1 : MeasureTheory.Integrable
          (fun z => ‖(Metric.closedBall (0 : ℂ) R).indicator (D ν.reverse) z‖ ^ q)
          MeasureTheory.volume := by
        have h := hMLp.integrable_norm_rpow
          (by simp only [ne_eq, ENNReal.ofReal_eq_zero]; linarith) ENNReal.ofReal_ne_top
        rwa [ENNReal.toReal_ofReal hq0.le] at h
      have h6 := h6a ν.reverse (by simp [hν])
      have hGae : G =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) R)]
          (fun z => ‖(Metric.closedBall (0 : ℂ) R).indicator (D ν.reverse) z‖ ^ q) := by
        refine (MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr ?_
        filter_upwards [h6, hzeroae] with z hzeq hzne hzball
        have hzU : z ∈ U := hRU (hball hzball)
        have hzΩ : z ∈ (U \ {(0 : ℂ)}) := ⟨hzU, by simpa using hzne⟩
        rw [Set.indicator_of_mem (hball hzball), hzeq hzΩ, List.reverse_reverse]
        simp only [hGdef, hFdef]
      have hGint : MeasureTheory.IntegrableOn G (Metric.ball (0 : ℂ) R) MeasureTheory.volume :=
        (hInt1.integrableOn).congr hGae.symm
      -- (6c) the scaling identity for the integrals
      have h6c : ∀ t : ℝ, 0 < t →
          ∫ z in Metric.ball (0 : ℂ) R, G z = ∫ z in Metric.ball (0 : ℂ) (t * R), G z := by
        intro t ht
        have hbrick := MeasureTheory.Measure.setIntegral_comp_smul_of_pos MeasureTheory.volume G
          (Metric.ball (0 : ℂ) R) ht
        rw [smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht,
          Complex.finrank_real_complex] at hbrick
        have hlhs : ∫ z in Metric.ball (0 : ℂ) R, G ((t : ℝ) • z)
            = (t ^ 2)⁻¹ * ∫ z in Metric.ball (0 : ℂ) R, G z := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.setIntegral_congr_ae Metric.isOpen_ball.measurableSet ?_
          filter_upwards [hzeroae] with z hz _
          exact hGscale t ht z hz
        rw [hlhs, smul_eq_mul] at hbrick
        have ht2 : ((t : ℝ) ^ 2)⁻¹ ≠ 0 := by positivity
        exact mul_left_cancel₀ ht2 hbrick
      -- (6d) the annulus has zero integral, so `G = 0` a.e. there
      have heq2 : ∫ z in Metric.ball (0 : ℂ) R, G z = ∫ z in Metric.ball (0 : ℂ) (R / 2), G z := by
        have h := h6c (1 / 2) (by norm_num)
        rwa [show (1 / 2 : ℝ) * R = R / 2 by ring] at h
      have hann : ∀ᵐ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) (R / 2)) → G z = 0 := by
        have hsub : Metric.ball (0 : ℂ) (R / 2) ⊆ Metric.ball (0 : ℂ) R :=
          Metric.ball_subset_ball (by linarith)
        have hmeas : MeasurableSet (Metric.ball (0 : ℂ) (R / 2)) :=
          Metric.isOpen_ball.measurableSet
        have hdiff : ∫ z in (Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) (R / 2)), G z = 0 := by
          have h := MeasureTheory.setIntegral_sdiff hmeas hGint hsub
          rw [h, heq2, sub_self]
        have hintd : MeasureTheory.IntegrableOn G
            (Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) (R / 2)) MeasureTheory.volume :=
          hGint.mono_set Set.sdiff_subset
        have h0 := (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall (fun z => hG0 z)) hintd).mp hdiff
        have hAmeas : MeasurableSet (Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) (R / 2)) :=
          Metric.isOpen_ball.measurableSet.diff hmeas
        have h1 := (MeasureTheory.ae_restrict_iff' hAmeas).mp h0
        filter_upwards [h1] with z hz hmem
        exact hz hmem
      -- `F` vanishes everywhere on the open annulus, by continuity
      have hAo : IsOpen {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < R} := by
        have h1 : IsOpen {z : ℂ | R / 2 < ‖z‖} := isOpen_lt continuous_const continuous_norm
        have h2 : IsOpen {z : ℂ | ‖z‖ < R} := isOpen_lt continuous_norm continuous_const
        have heqs : {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < R} = {z : ℂ | R / 2 < ‖z‖} ∩ {z : ℂ | ‖z‖ < R} :=
          rfl
        rw [heqs]
        exact h1.inter h2
      have hAosub : {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < R} ⊆ ({(0 : ℂ)}ᶜ : Set ℂ) := by
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h0
        rw [h0] at hz
        have h1 : R / 2 < ‖(0 : ℂ)‖ := hz.1
        rw [norm_zero] at h1
        linarith
      have hFann : ∀ z ∈ {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < R}, F z = 0 := by
        refine hdense _ hAo F (fun _ => 0) (hFcont.mono hAosub) continuousOn_const ?_
        filter_upwards [hann] with z hz hzA
        have hmem : z ∈ (Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) (R / 2)) := by
          refine ⟨?_, ?_⟩
          · simpa [Metric.mem_ball, dist_zero_right] using hzA.2
          · simp only [Metric.mem_ball, dist_zero_right, not_lt]
            exact le_of_lt hzA.1
        have hGz : G z = 0 := hz hmem
        rw [hGdef] at hGz
        simp only at hGz
        have hFz : ‖F z‖ = 0 := by
          by_contra hne
          have hpos : 0 < ‖F z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
          exact absurd hGz (Real.rpow_pos_of_pos hpos q).ne'
        exact norm_eq_zero.mp hFz
      -- spread from the annulus to every `z ≠ 0` by the scaling (16)
      intro z hz
      have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      obtain ⟨t, htdef⟩ : ∃ y : ℝ, y = (3 * R / 4) / ‖z‖ := ⟨_, rfl⟩
      have ht : 0 < t := by
        rw [htdef]
        positivity
      have htz : ‖(t : ℂ) * z‖ = 3 * R / 4 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, htdef]
        field_simp
      have htzA : ((t : ℂ) * z) ∈ {z : ℂ | R / 2 < ‖z‖ ∧ ‖z‖ < R} := by
        refine ⟨?_, ?_⟩ <;> rw [htz] <;> linarith
      have h := h16 t ht z hz
      rw [hFann _ htzA] at h
      have hc : ((t ^ (α - 2) : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact (Real.rpow_pos_of_pos ht _).ne'
      have hFz : F z = 0 := (mul_eq_zero.mp h.symm).resolve_left hc
      rw [hFdef] at hFz
      exact hFz
    -- (6e) the contradiction, in two branches
    rcases lt_or_eq_of_le hα1 with hαlt | hα1'
    · obtain ⟨z₀, hz₀n, hz₀⟩ := hstep3
      have hz₀ne : z₀ ≠ 0 := by
        rw [← norm_pos_iff, hz₀n]
        norm_num
      exact hz₀ (hstep2 (k + 1) z₀ hz₀ne (h0g hαlt) (fun ν hν => h17 ν hν z₀ hz₀ne))
    · exact hstep4 hα1' R hR (fun ν hν z hz _ => h17 ν hν z hz)
  exact ⟨hstep5, hstep6⟩
