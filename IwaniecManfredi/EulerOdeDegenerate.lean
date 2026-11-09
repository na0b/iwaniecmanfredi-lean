import IwaniecManfredi.LambdaCoef
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-- The one degenerate case of the Euler equation (35) that the paper's claim at
line 313 that the indicial roots are distinct misses: at `k = 0` and `p = 2` the
indicial polynomial is `(λ + n)²`, the two roots coincide at `-n`, and the
general solution is `(A + B log r) r^{-n}` rather than a combination of two
distinct powers.  Written out, (35) reads `r(r y')' + 2n r y' + n² y = 0`
there. -/
theorem EulerOdeDegenerate (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ → ℂ) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioo (0 : ℝ) 1))
    (hode : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ((r : ℝ) : ℂ) * deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s) r
        + ((2 * (n : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) * deriv y r
        + (((n : ℝ) ^ 2 : ℝ) : ℂ) * y r = 0) :
    ∃ Ac Bc : ℂ, ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      y r = (Ac + Bc * ((Real.log r : ℝ) : ℂ)) * ((r ^ (-(n : ℝ)) : ℝ) : ℂ) := by
  -- Write `n = m + 1`, so that `r ^ (n-1)` is the honest power `r ^ m` and
  -- `ring` can relate it to `r ^ n` and `r ^ (n+1)`.
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hIo : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hIp : IsPreconnected (Set.Ioo (0 : ℝ) 1) := (convex_Ioo (0 : ℝ) 1).isPreconnected
  -- `y` and `deriv y` are differentiable on the open interval.
  obtain ⟨hyd, hy1⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hIo).mp hy
  obtain ⟨hy1d, -⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hIo).mp hy1
  have hyA : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt y (deriv y r) r := fun r hr =>
    (hyd.differentiableAt (hIo.mem_nhds hr)).hasDerivAt
  have hy1A : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (deriv y) (deriv (deriv y) r) r := fun r hr =>
    (hy1d.differentiableAt (hIo.mem_nhds hr)).hasDerivAt
  -- `s ↦ (s : ℂ)` has derivative `1`.
  have hP : ∀ r : ℝ, HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 r := fun r => by
    simpa using (hasDerivAt_id r).ofReal_comp
  -- The derivative of `s ↦ (s : ℂ) ^ (m+1)`.
  have hPow : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1)) (((m : ℂ) + 1) * (r : ℂ) ^ m) r := by
    intro r
    have h := (hP r).fun_pow (m + 1)
    simp only [Nat.add_sub_cancel, mul_one] at h
    push_cast at h
    exact h
  -- The hypothesis, written out in `y'` and `y''`.
  have hode' : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (r : ℂ) ^ 2 * deriv (deriv y) r + (2 * (m : ℂ) + 3) * (r : ℂ) * deriv y r
        + ((m : ℂ) + 1) ^ 2 * y r = 0 := by
    intro r hr
    have hd1 : DifferentiableAt ℝ (fun s : ℝ => ((s : ℝ) : ℂ)) r := (hP r).differentiableAt
    have hd2 : DifferentiableAt ℝ (deriv y) r := (hy1A r hr).differentiableAt
    have hmul : deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s) r
        = deriv (fun s : ℝ => ((s : ℝ) : ℂ)) r * deriv y r
          + ((r : ℝ) : ℂ) * deriv (deriv y) r := deriv_fun_mul hd1 hd2
    have hone : deriv (fun s : ℝ => ((s : ℝ) : ℂ)) r = 1 := (hP r).deriv
    have h := hode r hr
    rw [hmul, hone] at h
    push_cast at h ⊢
    linear_combination h
  -- First integrating factor: `G r = r ^ (m+1) * (r y' + (m+1) y)` has zero derivative.
  have hGd : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * (((s : ℝ) : ℂ) * deriv y s + ((m : ℂ) + 1) * y s))
        0 r := by
    intro r hr
    have h2 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s + ((m : ℂ) + 1) * y s)
        (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r + ((m : ℂ) + 1) * deriv y r) r :=
      ((hP r).fun_mul (hy1A r hr)).add ((hyA r hr).const_mul ((m : ℂ) + 1))
    have h3 : HasDerivAt
        (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * (((s : ℝ) : ℂ) * deriv y s + ((m : ℂ) + 1) * y s))
        (((m : ℂ) + 1) * (r : ℂ) ^ m * (((r : ℝ) : ℂ) * deriv y r + ((m : ℂ) + 1) * y r)
          + ((r : ℝ) : ℂ) ^ (m + 1)
            * (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r + ((m : ℂ) + 1) * deriv y r))
        r := (hPow r).fun_mul h2
    have hz : ((m : ℂ) + 1) * (r : ℂ) ^ m * (((r : ℝ) : ℂ) * deriv y r + ((m : ℂ) + 1) * y r)
        + ((r : ℝ) : ℂ) ^ (m + 1)
          * (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r + ((m : ℂ) + 1) * deriv y r)
        = 0 := by
      have h := hode' r hr
      linear_combination (r : ℂ) ^ m * h
    rw [← hz]
    exact h3
  have hGdiff : DifferentiableOn ℝ
      (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * (((s : ℝ) : ℂ) * deriv y s + ((m : ℂ) + 1) * y s))
      (Set.Ioo (0 : ℝ) 1) := fun r hr => ((hGd r hr).differentiableAt).differentiableWithinAt
  obtain ⟨Bc, hBc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIp hGdiff
    (fun r hr => by simpa using (hGd r hr).deriv)
  -- Second integrating factor -- this is where the logarithm enters.
  have hHd : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * y s - Bc * ((Real.log s : ℝ) : ℂ)) 0 r := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt hr.1
    have hrC : ((r : ℝ) : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hrne
    have h2 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * y s)
        (((m : ℂ) + 1) * (r : ℂ) ^ m * y r + ((r : ℝ) : ℂ) ^ (m + 1) * deriv y r) r :=
      (hPow r).fun_mul (hyA r hr)
    have h3 : HasDerivAt (fun s : ℝ => Bc * ((Real.log s : ℝ) : ℂ)) (Bc * ((r⁻¹ : ℝ) : ℂ)) r :=
      ((Real.hasDerivAt_log hrne).ofReal_comp).const_mul Bc
    have h4 : HasDerivAt
        (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * y s - Bc * ((Real.log s : ℝ) : ℂ))
        (((m : ℂ) + 1) * (r : ℂ) ^ m * y r + ((r : ℝ) : ℂ) ^ (m + 1) * deriv y r
          - Bc * ((r⁻¹ : ℝ) : ℂ)) r := h2.sub h3
    have hz : ((m : ℂ) + 1) * (r : ℂ) ^ m * y r + ((r : ℝ) : ℂ) ^ (m + 1) * deriv y r
        - Bc * ((r⁻¹ : ℝ) : ℂ) = 0 := by
      have hb := hBc r hr
      have hinv : ((r⁻¹ : ℝ) : ℂ) = ((r : ℝ) : ℂ)⁻¹ := by push_cast; ring
      rw [hinv, sub_eq_zero, ← div_eq_mul_inv, eq_div_iff hrC]
      linear_combination hb
    rw [← hz]
    exact h4
  have hHdiff : DifferentiableOn ℝ
      (fun s : ℝ => ((s : ℝ) : ℂ) ^ (m + 1) * y s - Bc * ((Real.log s : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) 1) := fun r hr => ((hHd r hr).differentiableAt).differentiableWithinAt
  obtain ⟨Ac, hAc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIp hHdiff
    (fun r hr => by simpa using (hHd r hr).deriv)
  -- Divide by `r ^ (m+1) ≠ 0`.
  refine ⟨Ac, Bc, ?_⟩
  intro r hr
  have h := hAc r hr
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using ne_of_gt hr.1
  have hpowne : ((r : ℝ) : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hrC
  have hrpow : ((r ^ (-(((m + 1 : ℕ)) : ℝ)) : ℝ) : ℂ) = (((r : ℝ) : ℂ) ^ (m + 1))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hr.1), Real.rpow_natCast]
    push_cast
    ring
  rw [hrpow, inv_eq_one_div, mul_one_div, eq_div_iff hpowne]
  linear_combination h
