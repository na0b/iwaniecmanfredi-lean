import IwaniecManfredi.EulerOdeSolution
import IwaniecManfredi.EulerOdeDegenerate

/-- Formula (36) of the paper: a solution of the Euler equation (35) on `(0,1)`
which stays continuous up to `r = 0` vanishes identically when `|k| < n`, and is
`A_k r^{λ_k}` when `|k| ≥ n`.  The sign of the exponent `λ⁺` is governed by `|k|`
against `n` in three regimes: negative for `|k| < n`, exactly zero for
`|k| = n` -- where `r^{λ⁺} ≡ 1` is bounded and `A⁺` need not vanish, which is
how the `k = ±n` coefficient comes out constant -- and positive for
`|k| > n`.  No non-degeneracy is assumed: at the one pair `k = 0`, `p = 2` where
the indicial roots coincide the conclusion still holds, because there
`|k| = 0 < n` and the extra solution `(log r) r^{-n}` is unbounded as
`r → 0⁺` too. -/
theorem FourierCoefForm36 (n : ℕ) (p : ℝ) (k : ℤ) (hn : 1 ≤ n) (hp : 1 < p)
    (a : ℝ → ℂ) (hcont : ContinuousOn a (Set.Ico (0 : ℝ) 1))
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) a (Set.Ioo (0 : ℝ) 1))
    (hode : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ((r : ℝ) : ℂ) * deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv a s) r
        + ((p * (n : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) * deriv a r
        + ((((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) : ℝ) : ℂ) * a r = 0) :
    (k.natAbs < n → ∀ r ∈ Set.Ico (0 : ℝ) 1, a r = 0) ∧
    (n ≤ k.natAbs → ∃ A : ℂ, ∀ r ∈ Set.Ico (0 : ℝ) 1,
      a r = A * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)) := by
  classical
  -- ## Elementary positivity facts
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hnp : (0 : ℝ) < (n : ℝ) * p := by positivity
  have hkabs : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by simp [sq_abs]
  -- ## Step 0b: `a` is bounded on `[0, 1/2]`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1/2)).exists_bound_of_continuousOn
    (hcont.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (by norm_num)⟩))
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl _, by norm_num⟩)
  -- ## The punctured-neighbourhood filter at `0`, and the two limit tools
  have hNB : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) (1/2))).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0:ℝ) ≠ 1/2)]
    exact ⟨le_refl _, by norm_num⟩
  have hsq : ∀ (x : ℝ) (f : ℝ → ℝ), 0 ≤ x →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) (1/2))) (nhds 0) →
      (∀ r ∈ Set.Ioo (0 : ℝ) (1/2), x ≤ f r) → x = 0 := by
    intro x f hx hf hle
    exact le_antisymm (ge_of_tendsto hf (Filter.eventually_of_mem self_mem_nhdsWithin hle)) hx
  have hrpow0 : ∀ q : ℝ, 0 < q →
      Filter.Tendsto (fun r : ℝ => (r ^ q : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) (1/2))) (nhds 0) := by
    intro q hq
    have h := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hq)] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- ## The `r = 0` endpoint: a continuous function on `[0,1)` is determined on `(0,1)`
  have hNB1 : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨le_refl _, by norm_num⟩
  have hta : Filter.Tendsto a (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) (nhds (a 0)) :=
    (hcont 0 ⟨le_refl _, by norm_num⟩).mono_left
      (nhdsWithin_mono _ Set.Ioo_subset_Ico_self)
  have hendpoint : ∀ (g : ℝ → ℂ),
      Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) (nhds (g 0)) →
      (∀ r ∈ Set.Ioo (0 : ℝ) 1, a r = g r) → ∀ r ∈ Set.Ico (0 : ℝ) 1, a r = g r := by
    intro g hg heq r hr
    rcases eq_or_lt_of_le hr.1 with h0 | h0
    · have h00 : a 0 = g 0 := by
        refine tendsto_nhds_unique hta ?_
        refine hg.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (heq s hs).symm
      rw [← h0]; exact h00
    · exact heq r ⟨h0, hr.2⟩
  -- ## The non-degenerate / degenerate split (Step 0a)
  by_cases hdeg : k ≠ 0 ∨ p ≠ 2
  · -- ### Non-degenerate case: `k ≠ 0` or `p ≠ 2`
    obtain ⟨Ap, Am, hsol⟩ := EulerOdeSolution n p k hn hp hdeg a hsm hode
    obtain ⟨S, hS0, hS2, hLp⟩ : ∃ S : ℝ, 0 ≤ S ∧
        S ^ 2 = 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 ∧
        LambdaCoef n k.natAbs p = (-((n : ℝ) * p) + S) / 2 := by
      refine ⟨Real.sqrt (4 * ((k.natAbs : ℕ) : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2),
        Real.sqrt_nonneg _, ?_, ?_⟩
      · rw [Real.sq_sqrt (by positivity), hkabs]
      · unfold LambdaCoef; ring
    -- (1): the discriminant is positive, so `S > 0`
    have hD0 : (0 : ℝ) < 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      rcases hdeg with hk | hpp
      · have hk0 : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
        have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := sq_pos_of_ne_zero hk0
        have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 := by positivity
        nlinarith
      · have hpp0 : p - 2 ≠ 0 := fun h => hpp (by linarith)
        have hp2 : (0 : ℝ) < (p - 2) ^ 2 := sq_pos_of_ne_zero hpp0
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
        have hnn : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) := by positivity
        nlinarith
    have hSpos : 0 < S := by nlinarith [hS2, hD0, hS0]
    -- (2): `λ⁻ < 0`
    have hLmval : -(p * (n : ℝ)) - LambdaCoef n k.natAbs p = (-((n : ℝ) * p) - S) / 2 := by
      rw [hLp]; ring
    have hLmneg : -(p * (n : ℝ)) - LambdaCoef n k.natAbs p < 0 := by
      rw [hLmval]; nlinarith
    -- `λ⁺ - λ⁻ = S`
    have hdiff : LambdaCoef n k.natAbs p - (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p) = S := by
      rw [hLp]; ring
    -- ### Step 3: `A⁻ = 0`
    have hAmbound : ∀ r ∈ Set.Ioo (0 : ℝ) (1/2),
        ‖Am‖ ≤ M * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)))
          + ‖Ap‖ * (r ^ S) := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, by linarith [hr.2]⟩
      have hMa : ‖a r‖ ≤ M := hM r ⟨hr0.le, hr.2.le⟩
      have hra := hsol r hrIoo
      have hposL : (0 : ℝ) < r ^ LambdaCoef n k.natAbs p := Real.rpow_pos_of_pos hr0 _
      have hposM : (0 : ℝ) < r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p) :=
        Real.rpow_pos_of_pos hr0 _
      have hposN : (0 : ℝ) < r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)) :=
        Real.rpow_pos_of_pos hr0 _
      -- `‖Am‖ * r^{λ⁻} ≤ M + ‖Ap‖ * r^{λ⁺}`
      have hstep : ‖Am‖ * (r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))
          ≤ M + ‖Ap‖ * (r ^ LambdaCoef n k.natAbs p) := by
        have he : Am * (((r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p) : ℝ)) : ℂ)
            = a r - Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ) := by
          rw [hra]; ring
        have h1 : ‖Am‖ * (r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))
            = ‖a r - Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ)‖ := by
          rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposM]
        have h2 : ‖Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ)‖
            = ‖Ap‖ * (r ^ LambdaCoef n k.natAbs p) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposL]
        have h3 := norm_sub_le (a r) (Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ))
        rw [h1]
        rw [h2] at h3
        linarith
      -- multiply by `r^{-λ⁻} > 0` and collect exponents
      have hcancel : (r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))
          * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))) = 1 := by
        rw [← Real.rpow_add hr0,
          show (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)
            + (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)) = (0 : ℝ) from by ring,
          Real.rpow_zero]
      have hcollect : (r ^ LambdaCoef n k.natAbs p)
          * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))) = r ^ S := by
        rw [← Real.rpow_add hr0,
          show LambdaCoef n k.natAbs p
            + (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)) = S from by linarith [hdiff]]
      calc ‖Am‖ = ‖Am‖ * ((r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))
              * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)))) := by rw [hcancel, mul_one]
        _ = (‖Am‖ * (r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)))
              * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))) := by ring
        _ ≤ (M + ‖Ap‖ * (r ^ LambdaCoef n k.natAbs p))
              * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))) :=
            mul_le_mul_of_nonneg_right hstep hposN.le
        _ = M * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)))
              + ‖Ap‖ * ((r ^ LambdaCoef n k.natAbs p)
                * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)))) := by ring
        _ = M * (r ^ (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p))) + ‖Ap‖ * (r ^ S) := by
            rw [hcollect]
    have hAm0 : Am = 0 := by
      refine norm_eq_zero.mp (hsq ‖Am‖ _ (norm_nonneg _) ?_ hAmbound)
      have h1 := (hrpow0 (-(-(p * (n : ℝ)) - LambdaCoef n k.natAbs p)) (by linarith)).const_mul M
      have h2 := (hrpow0 S hSpos).const_mul ‖Ap‖
      simpa using h1.add h2
    -- (7): `a r = A⁺ r^{λ⁺}` on `(0,1)`
    have hsol2 : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        a r = Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ) := by
      intro r hr
      rw [hsol r hr, hAm0]; ring
    refine ⟨?_, ?_⟩
    · -- ### Step 4: `|k| < n`
      intro hlt
      have hk2 : (k : ℝ) ^ 2 < (n : ℝ) ^ 2 := by
        have h1 : ((k.natAbs : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt
        have h2 : (0 : ℝ) ≤ ((k.natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [hkabs]
      have hLneg : LambdaCoef n k.natAbs p < 0 := by
        have hlt2 : S ^ 2 < ((n : ℝ) * p) ^ 2 := by rw [hS2]; nlinarith
        have hSlt : S < (n : ℝ) * p := by nlinarith
        rw [hLp]; linarith
      have hApbound : ∀ r ∈ Set.Ioo (0 : ℝ) (1/2),
          ‖Ap‖ ≤ M * (r ^ (-LambdaCoef n k.natAbs p)) := by
        intro r hr
        have hr0 : 0 < r := hr.1
        have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, by linarith [hr.2]⟩
        have hMa : ‖a r‖ ≤ M := hM r ⟨hr0.le, hr.2.le⟩
        have hposL : (0 : ℝ) < r ^ LambdaCoef n k.natAbs p := Real.rpow_pos_of_pos hr0 _
        have hposN : (0 : ℝ) < r ^ (-LambdaCoef n k.natAbs p) := Real.rpow_pos_of_pos hr0 _
        have h1 : ‖Ap‖ * (r ^ LambdaCoef n k.natAbs p) = ‖a r‖ := by
          rw [hsol2 r hrIoo, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposL]
        have hcancel : (r ^ LambdaCoef n k.natAbs p) * (r ^ (-LambdaCoef n k.natAbs p)) = 1 := by
          rw [← Real.rpow_add hr0]; simp
        calc ‖Ap‖ = (‖Ap‖ * (r ^ LambdaCoef n k.natAbs p)) * (r ^ (-LambdaCoef n k.natAbs p)) := by
              rw [mul_assoc, hcancel, mul_one]
          _ = ‖a r‖ * (r ^ (-LambdaCoef n k.natAbs p)) := by rw [h1]
          _ ≤ M * (r ^ (-LambdaCoef n k.natAbs p)) := mul_le_mul_of_nonneg_right hMa hposN.le
      have hAp0 : Ap = 0 := by
        refine norm_eq_zero.mp (hsq ‖Ap‖ _ (norm_nonneg _) ?_ hApbound)
        simpa using (hrpow0 (-LambdaCoef n k.natAbs p) (by linarith)).const_mul M
      have hzero : ∀ r ∈ Set.Ioo (0 : ℝ) 1, a r = (fun _ : ℝ => (0 : ℂ)) r := by
        intro r hr
        rw [hsol2 r hr, hAp0]; ring
      exact hendpoint (fun _ => (0 : ℂ)) tendsto_const_nhds hzero
    · -- ### Step 5: `|k| ≥ n`
      intro hge
      have hk2 : (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
        have h1 : (n : ℝ) ≤ ((k.natAbs : ℕ) : ℝ) := by exact_mod_cast hge
        nlinarith [hkabs]
      have hLnn : 0 ≤ LambdaCoef n k.natAbs p := by
        have hle2 : ((n : ℝ) * p) ^ 2 ≤ S ^ 2 := by rw [hS2]; nlinarith
        have hSge : (n : ℝ) * p ≤ S := by nlinarith
        rw [hLp]; linarith
      refine ⟨Ap, ?_⟩
      refine hendpoint (fun r : ℝ => Ap * (((r ^ LambdaCoef n k.natAbs p : ℝ)) : ℂ)) ?_ hsol2
      refine Filter.Tendsto.const_mul Ap ?_
      refine (Complex.continuous_ofReal.continuousAt.tendsto).comp ?_
      exact (Real.continuousAt_rpow_const 0 (LambdaCoef n k.natAbs p)
        (Or.inr hLnn)).tendsto.mono_left nhdsWithin_le_nhds
  · -- ### Degenerate case: `k = 0` and `p = 2`
    have hk0 : k = 0 := by
      by_contra h
      exact hdeg (Or.inl h)
    have hp2 : p = 2 := by
      by_contra h
      exact hdeg (Or.inr h)
    subst hk0
    subst hp2
    have hode' : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        ((r : ℝ) : ℂ) * deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv a s) r
          + ((2 * (n : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) * deriv a r
          + (((n : ℝ) ^ 2 : ℝ) : ℂ) * a r = 0 := by
      intro r hr
      have h := hode r hr
      push_cast at h ⊢
      linear_combination h
    obtain ⟨Ac, Bc, hsol⟩ := EulerOdeDegenerate n hn a hsm hode'
    have hrpowge : ∀ r : ℝ, 0 < r → r ≤ 1 → 1 ≤ r ^ (-(n : ℝ)) := by
      intro r hr0 hr1
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 (by linarith)
    have hABbound : ∀ r ∈ Set.Ioc (0 : ℝ) (1/2),
        ‖Ac + Bc * (((Real.log r : ℝ)) : ℂ)‖ ≤ M := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hr1 : r ≤ 1 := by linarith [hr.2]
      have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, by linarith [hr.2]⟩
      have hMa : ‖a r‖ ≤ M := hM r ⟨hr0.le, hr.2⟩
      have hpos : (0 : ℝ) < r ^ (-(n : ℝ)) := Real.rpow_pos_of_pos hr0 _
      have hnorm : ‖a r‖ = ‖Ac + Bc * (((Real.log r : ℝ)) : ℂ)‖ * (r ^ (-(n : ℝ))) := by
        rw [hsol r hrIoo, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith [norm_nonneg (Ac + Bc * (((Real.log r : ℝ)) : ℂ)), hrpowge r hr0 hr1]
    -- `B = 0`
    have hBc0 : Bc = 0 := by
      by_contra hB
      have hBpos : 0 < ‖Bc‖ := norm_pos_iff.mpr hB
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hTlog2 : Real.log 2 ≤ max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) := le_max_left _ _
      have hTge : (M + ‖Ac‖ + 1) / ‖Bc‖ ≤ max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) :=
        le_max_right _ _
      have hT0 : 0 < max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) :=
        lt_of_lt_of_le hlog2pos hTlog2
      have hr0 : 0 < Real.exp (-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖)) := Real.exp_pos _
      have hrle : Real.exp (-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖)) ≤ 1/2 := by
        have h2 : Real.exp (-Real.log 2) = 1/2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
          norm_num
        calc Real.exp (-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖))
            ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
          _ = 1/2 := h2
      have hb := hABbound _ ⟨hr0, hrle⟩
      rw [Real.log_exp] at hb
      have hnz : ‖Bc * (((-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) : ℝ)) : ℂ)‖
          = ‖Bc‖ * max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hT0]
      have hsub := norm_sub_le (Ac + Bc * (((-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) : ℝ)) : ℂ)) Ac
      have hsimp : (Ac + Bc * (((-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) : ℝ)) : ℂ)) - Ac
          = Bc * (((-max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) : ℝ)) : ℂ) := by ring
      rw [hsimp, hnz] at hsub
      have hbig : M + ‖Ac‖ + 1 ≤ max (Real.log 2) ((M + ‖Ac‖ + 1) / ‖Bc‖) * ‖Bc‖ :=
        (div_le_iff₀ hBpos).mp hTge
      nlinarith
    -- `A = 0`
    have hsol2 : ∀ r ∈ Set.Ioo (0 : ℝ) 1, a r = Ac * (((r ^ (-(n : ℝ)) : ℝ)) : ℂ) := by
      intro r hr
      rw [hsol r hr, hBc0]; ring
    have hAcbound : ∀ r ∈ Set.Ioo (0 : ℝ) (1/2), ‖Ac‖ ≤ M * r := by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hr1 : r ≤ 1 := by linarith [hr.2]
      have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, by linarith [hr.2]⟩
      have hMa : ‖a r‖ ≤ M := hM r ⟨hr0.le, hr.2.le⟩
      have hpos : (0 : ℝ) < r ^ (-(n : ℝ)) := Real.rpow_pos_of_pos hr0 _
      have hnorm : ‖a r‖ = ‖Ac‖ * (r ^ (-(n : ℝ))) := by
        rw [hsol2 r hrIoo, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      -- `r^{-n} ≥ r⁻¹`, i.e. `r * r^{-n} ≥ 1`
      have hrn : r ^ (n : ℝ) ≤ r := by
        have h := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hn1
        rwa [Real.rpow_one] at h
      have hrnpos : (0 : ℝ) < r ^ (n : ℝ) := Real.rpow_pos_of_pos hr0 _
      have hinv : 1 ≤ r * (r ^ (-(n : ℝ))) := by
        rw [Real.rpow_neg hr0.le]
        rw [le_mul_inv_iff₀ hrnpos]
        linarith
      nlinarith [norm_nonneg Ac]
    have hAc0 : Ac = 0 := by
      refine norm_eq_zero.mp (hsq ‖Ac‖ _ (norm_nonneg _) ?_ hAcbound)
      have h : Filter.Tendsto (fun x : ℝ => M * x) (nhds (0:ℝ)) (nhds (M * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    refine ⟨?_, ?_⟩
    · intro _
      have hzero : ∀ r ∈ Set.Ioo (0 : ℝ) 1, a r = (fun _ : ℝ => (0 : ℂ)) r := by
        intro r hr
        rw [hsol2 r hr, hAc0]; ring
      exact hendpoint (fun _ => (0 : ℂ)) tendsto_const_nhds hzero
    · intro hge
      simp only [Int.natAbs_zero] at hge
      omega
