import IwaniecManfredi.FourierCoefForm36
import IwaniecManfredi.FourierCoefOde
import IwaniecManfredi.QCDistortionPolar
import IwaniecManfredi.LambdaEpsEstimates
import IwaniecManfredi.LambdaLinearLowerBound
import IwaniecManfredi.GammaRatioMinAtOne
import IwaniecManfredi.ParsevalOnCircle

set_option maxHeartbeats 1600000


open MeasureTheory

/-- The energy identity of Section 4 of the paper -- the Parseval evaluation of
`∬_B |H_r|² dσ` in terms of the coefficients `A_k` -- together with the
coefficient bound (22) of Theorem 2 in both directions.  The constant `C` is
quantified before `H`, so it depends only on `n`, `p` and `K`.  The hypothesis
that `H` solves (18) is indispensable and not implied by the coefficient
hypotheses: the latter pin `a_j` only for `|j| ≥ n`, while Parseval runs over
all of `ℤ`, so a free mode such as `a_0(r) = r` would add `π` to the left-hand
side.  Equation (18) kills those modes through (33) and (36).  The two
`Summable` clauses are the paper's own `< ∞` in (22); without them the
inequalities would be vacuous, since the sum of a non-summable family is `0`
by convention. -/
theorem EnergyIdentity (n : ℕ) (p : ℝ) (K : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℂ → ℂ) (A : ℤ → ℂ),
        ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1} →
        (∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ) →
        SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H →
        QuasiregularOn K {ξ : ℂ | ‖ξ‖ < 1} H →
        IntegrableOn (fun ξ : ℂ => ‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)
          {ξ : ℂ | ‖ξ‖ < 1} volume →
        (∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
          FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)) →
        (∀ k : ℤ, (n : ℤ) < k →
          A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k)) →
        Summable (fun m : ℕ => LambdaCoef n (n + 1 + m) p
            * (1 + EpsCoef n (n + 1 + m) p ^ 2) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) ∧
        ((∫ r in (0 : ℝ)..1, r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
          = Real.pi * ∑' m : ℕ, LambdaCoef n (n + 1 + m) p
              * (1 + EpsCoef n (n + 1 + m) p ^ 2) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) ∧
        Summable (fun m : ℕ =>
            ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) ∧
        (∑' m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
          ≤ C * ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) ∧
        ((∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2))
          ≤ C * ∑' m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  -- `γ_n = λ_{n+1}(n,p) > 0`, by part (a) of `GammaRatioMinAtOne`
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  -- the two constants of Steps 4 and 5; both depend only on `n`, `p`, `K`
  set C₁ : ℝ := 2 * ((n : ℝ) + 1) / (Real.pi * GammaExp n p * (1 + K⁻¹ ^ 2)) with hC1def
  set C₂ : ℝ := (1 + K ^ 2) * Real.pi * Real.sqrt (p - 1) with hC2def
  have hC1pos : 0 < C₁ := by
    rw [hC1def]
    refine div_pos (by positivity) ?_
    exact mul_pos (mul_pos hpi hγ) (by positivity)
  have hC2pos : 0 < C₂ := by
    rw [hC2def]
    have hs : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr hp1
    have hKsq : (0 : ℝ) < 1 + K ^ 2 := by positivity
    exact mul_pos (mul_pos hKsq hpi) hs
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC1pos (le_max_left _ _), ?_⟩
  intro H A hc hdiff h18 hqr hint hcoef heps
  -- ## Step 0: the hypotheses of the Section-4 nodes
  have hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H := hqr.2.1
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  obtain ⟨h1a, h1b, h1c, h1d, h1e, h1f⟩ := FourierCoefRegularity n H hc hw hdiff
  obtain ⟨hode33, hode35, hsmooth⟩ := FourierCoefOde n p hn hp H hc hw hdiff h18
  -- the low modes vanish identically, by (36)
  have hvanish : ∀ j : ℤ, j.natAbs < n → ∀ r ∈ Set.Ico (0 : ℝ) 1,
      FourierCoefOfH n H j r = 0 := by
    intro j hj
    exact (FourierCoefForm36 n p j hn hp (FourierCoefOfH n H j) (h1a j) (hsmooth j)
      (hode35 j)).1 hj
  -- ## Step 1: the Fourier coefficients of `H_r`
  have hstep1 : ∀ᵐ r : ℝ, ∀ j : ℤ, r ∈ Set.Ioo (0 : ℝ) 1 →
      ‖FourierCoefOfH n (HRad H) j r‖ ^ 2
        = if n ≤ j.natAbs
            then ‖A j‖ ^ 2 * LambdaCoef n j.natAbs p ^ 2
                  * r ^ (2 * LambdaCoef n j.natAbs p - 2)
            else 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    by_cases hj : n ≤ j.natAbs
    · filter_upwards [h1c j] with r hcr hrmem
      rw [if_pos hj]
      obtain ⟨hr0, hr1⟩ := hrmem
      have hrmem' : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hr1⟩
      have hjabs : (n : ℤ) ≤ |j| := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hj
      have hd : HasDerivAt (fun s : ℝ => A j * ((s ^ LambdaCoef n j.natAbs p : ℝ) : ℂ))
          (A j * (((LambdaCoef n j.natAbs p)
            * r ^ ((LambdaCoef n j.natAbs p) - 1) : ℝ) : ℂ)) r := by
        have h1 : HasDerivAt (fun s : ℝ => (s ^ LambdaCoef n j.natAbs p : ℝ))
            ((LambdaCoef n j.natAbs p) * r ^ ((LambdaCoef n j.natAbs p) - 1)) r :=
          Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hr0))
        exact (h1.ofReal_comp).const_mul _
      have hd2 : HasDerivAt (FourierCoefOfH n H j)
          (A j * (((LambdaCoef n j.natAbs p)
            * r ^ ((LambdaCoef n j.natAbs p) - 1) : ℝ) : ℂ)) r := by
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioo.mem_nhds hrmem'] with s hs
        exact hcoef j hjabs s hs
      have hexp : (r ^ (LambdaCoef n j.natAbs p - 1)) ^ 2
          = r ^ (2 * LambdaCoef n j.natAbs p - 2) := by
        rw [← Real.rpow_natCast (r ^ (LambdaCoef n j.natAbs p - 1)) 2, ← Real.rpow_mul hr0.le]
        congr 1
        push_cast
        ring
      rw [(hcr hrmem').unique hd2, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
        sq_abs, mul_pow, hexp]
      ring
    · filter_upwards [h1c j] with r hcr hrmem
      rw [if_neg hj]
      obtain ⟨hr0, hr1⟩ := hrmem
      have hrmem' : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hr1⟩
      have hd2 : HasDerivAt (FourierCoefOfH n H j) 0 r := by
        refine (hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioo.mem_nhds hrmem'] with s hs
        exact hvanish j (by omega) s ⟨hs.1.le, hs.2⟩
      rw [(hcr hrmem').unique hd2]
      simp
  -- ## measurability of the radial derivative
  have hev : Continuous (fun q : (ℂ →L[ℝ] ℂ) × ℂ => q.1 q.2) :=
    isBoundedBilinearMap_apply.continuous
  have hRadmeas : Measurable (HRad H) := by
    have h1 : Measurable (fun ζ : ℂ => ((fderiv ℝ H ζ), ζ / ((‖ζ‖ : ℝ) : ℂ))) :=
      (measurable_fderiv ℝ H).prodMk (by fun_prop)
    exact hev.measurable.comp h1
  have hcimeas : ∀ r : ℝ,
      Measurable (fun θ : ℝ => ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro r; fun_prop
  -- ## Step 2: Parseval on each circle, and the fold of `j` with `-j`
  have hstep2 : ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      IntegrableOn (fun θ : ℝ => ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        (Set.Ioc (0 : ℝ) (2 * Real.pi)) volume →
      HasSum (fun k : ℕ => 2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)))
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) := by
    filter_upwards [hstep1] with r h1r hrmem hL2
    obtain ⟨hr0, hr1⟩ := hrmem
    have hrmem' : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hr1⟩
    -- Parseval for the restriction of `H_r` to the circle of radius `r`
    have hpar := ParsevalOnCircle
      (fun θ : ℝ => HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      (hRadmeas.comp (hcimeas r)) hL2
    have hcoefeq : ∀ m : ℤ,
        (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)
          = FourierCoefOfH n (HRad H) (m + (n : ℤ)) r := by
      intro m
      rw [FourierCoefOfH]
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      congr 2
      push_cast
      ring
    rw [show (fun m : ℤ => 2 * Real.pi *
          ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
        = (fun m : ℤ => 2 * Real.pi * ‖FourierCoefOfH n (HRad H) (m + (n : ℤ)) r‖ ^ 2) from
      funext (fun m => by rw [hcoefeq m])] at hpar
    -- reindex `m ↦ j = m + n`
    have hpar2 : HasSum (fun j : ℤ => 2 * Real.pi * ‖FourierCoefOfH n (HRad H) j r‖ ^ 2)
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) :=
      (Equiv.addRight ((n : ℤ))).hasSum_iff.mp hpar
    -- the value of each term
    set g : ℤ → ℝ := fun j => 2 * Real.pi * ‖FourierCoefOfH n (HRad H) j r‖ ^ 2 with hgdef
    have hgval : ∀ j : ℤ, g j
        = if n ≤ j.natAbs
            then 2 * Real.pi * (‖A j‖ ^ 2 * LambdaCoef n j.natAbs p ^ 2
                  * r ^ (2 * LambdaCoef n j.natAbs p - 2))
            else 0 := by
      intro j
      rw [hgdef]
      simp only
      rw [h1r j hrmem']
      by_cases hj : n ≤ j.natAbs
      · rw [if_pos hj, if_pos hj]
      · rw [if_neg hj, if_neg hj]; ring
    have hlamn : LambdaCoef n n p = 0 := (LambdaEpsEstimates n p hn hp).1
    have hgzero : ∀ j : ℤ, j.natAbs ≤ n → g j = 0 := by
      intro j hj
      rw [hgval j]
      rcases lt_or_eq_of_le hj with h | h
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega), h, hlamn]
        ring
    have hgnonneg : ∀ j : ℤ, 0 ≤ g j := by
      intro j
      rw [hgdef]
      positivity
    -- the two half-sums
    set gp : ℤ → ℝ := fun j => if (n : ℤ) + 1 ≤ j then g j else 0 with hgpdef
    set gm : ℤ → ℝ := fun j => if j ≤ -((n : ℤ) + 1) then g j else 0 with hgmdef
    have hgp0 : ∀ j : ℤ, 0 ≤ gp j := by
      intro j
      show (0 : ℝ) ≤ if (n : ℤ) + 1 ≤ j then g j else 0
      by_cases h : (n : ℤ) + 1 ≤ j
      · rw [if_pos h]; exact hgnonneg j
      · rw [if_neg h]
    have hgm0 : ∀ j : ℤ, 0 ≤ gm j := by
      intro j
      show (0 : ℝ) ≤ if j ≤ -((n : ℤ) + 1) then g j else 0
      by_cases h : j ≤ -((n : ℤ) + 1)
      · rw [if_pos h]; exact hgnonneg j
      · rw [if_neg h]
    have hgple : ∀ j : ℤ, gp j ≤ g j := by
      intro j
      show (if (n : ℤ) + 1 ≤ j then g j else 0) ≤ g j
      by_cases h : (n : ℤ) + 1 ≤ j
      · rw [if_pos h]
      · rw [if_neg h]; exact hgnonneg j
    have hgmle : ∀ j : ℤ, gm j ≤ g j := by
      intro j
      show (if j ≤ -((n : ℤ) + 1) then g j else 0) ≤ g j
      by_cases h : j ≤ -((n : ℤ) + 1)
      · rw [if_pos h]
      · rw [if_neg h]; exact hgnonneg j
    have hsplit : ∀ j : ℤ, gp j + gm j = g j := by
      intro j
      show (if (n : ℤ) + 1 ≤ j then g j else 0)
        + (if j ≤ -((n : ℤ) + 1) then g j else 0) = g j
      by_cases h1 : (n : ℤ) + 1 ≤ j
      · have h2 : ¬ (j ≤ -((n : ℤ) + 1)) := by omega
        rw [if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : j ≤ -((n : ℤ) + 1)
        · rw [if_neg h1, if_pos h2, zero_add]
        · rw [if_neg h1, if_neg h2, add_zero]
          exact (hgzero j (by omega)).symm
    have hsg : Summable g := hpar2.summable
    have hsgp : Summable gp := Summable.of_nonneg_of_le hgp0 hgple hsg
    have hsgm : Summable gm := Summable.of_nonneg_of_le hgm0 hgmle hsg
    have htot : (∑' j : ℤ, gp j) + (∑' j : ℤ, gm j)
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 := by
      refine HasSum.unique ?_ hpar2
      have h := hsgp.hasSum.add hsgm.hasSum
      exact h.congr_fun (fun j => (hsplit j).symm)
    -- each half-sum as a sum over `ℕ`
    have hinjp : Function.Injective (fun k : ℕ => (n : ℤ) + 1 + (k : ℤ)) := by
      intro a b hab
      simp only at hab
      omega
    have hinjm : Function.Injective (fun k : ℕ => -((n : ℤ) + 1 + (k : ℤ))) := by
      intro a b hab
      simp only at hab
      omega
    have hzerop : ∀ x : ℤ, x ∉ Set.range (fun k : ℕ => (n : ℤ) + 1 + (k : ℤ)) → gp x = 0 := by
      intro x hx
      show (if (n : ℤ) + 1 ≤ x then g x else 0) = 0
      refine if_neg ?_
      intro hle
      refine hx ⟨(x - (n : ℤ) - 1).toNat, ?_⟩
      show (n : ℤ) + 1 + (((x - (n : ℤ) - 1).toNat : ℕ) : ℤ) = x
      omega
    have hzerom : ∀ x : ℤ, x ∉ Set.range (fun k : ℕ => -((n : ℤ) + 1 + (k : ℤ))) → gm x = 0 := by
      intro x hx
      show (if x ≤ -((n : ℤ) + 1) then g x else 0) = 0
      refine if_neg ?_
      intro hle
      refine hx ⟨(-x - (n : ℤ) - 1).toNat, ?_⟩
      show -((n : ℤ) + 1 + (((-x - (n : ℤ) - 1).toNat : ℕ) : ℤ)) = x
      omega
    have hNp : HasSum (fun k : ℕ => g ((n : ℤ) + 1 + (k : ℤ))) (∑' j : ℤ, gp j) := by
      have h := (hinjp.hasSum_iff hzerop).mpr hsgp.hasSum
      refine h.congr_fun (fun k => ?_)
      show g ((n : ℤ) + 1 + (k : ℤ))
        = (if (n : ℤ) + 1 ≤ (n : ℤ) + 1 + (k : ℤ) then g ((n : ℤ) + 1 + (k : ℤ)) else 0)
      rw [if_pos (by omega : (n : ℤ) + 1 ≤ (n : ℤ) + 1 + (k : ℤ))]
    have hNm : HasSum (fun k : ℕ => g (-((n : ℤ) + 1 + (k : ℤ)))) (∑' j : ℤ, gm j) := by
      have h := (hinjm.hasSum_iff hzerom).mpr hsgm.hasSum
      refine h.congr_fun (fun k => ?_)
      show g (-((n : ℤ) + 1 + (k : ℤ)))
        = (if -((n : ℤ) + 1 + (k : ℤ)) ≤ -((n : ℤ) + 1)
          then g (-((n : ℤ) + 1 + (k : ℤ))) else 0)
      rw [if_pos (by omega : -((n : ℤ) + 1 + (k : ℤ)) ≤ -((n : ℤ) + 1))]
    -- the fold
    have hfold : ∀ k : ℕ, g ((n : ℤ) + 1 + (k : ℤ)) + g (-((n : ℤ) + 1 + (k : ℤ)))
        = 2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)) := by
      intro k
      have hnat1 : ((n : ℤ) + 1 + (k : ℤ)).natAbs = n + 1 + k := by omega
      have hnat2 : (-((n : ℤ) + 1 + (k : ℤ))).natAbs = n + 1 + k := by omega
      have hAneg : ‖A (-((n : ℤ) + 1 + (k : ℤ)))‖ ^ 2
          = EpsCoef n (n + 1 + k) p ^ 2 * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2 := by
        rw [heps ((n : ℤ) + 1 + (k : ℤ)) (by omega), hnat1, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, RCLike.norm_conj, mul_pow, sq_abs]
      rw [hgval, hgval, if_pos (by omega : n ≤ ((n : ℤ) + 1 + (k : ℤ)).natAbs),
        if_pos (by omega : n ≤ (-((n : ℤ) + 1 + (k : ℤ))).natAbs), hnat1, hnat2, hAneg]
      ring
    have hres := hNp.add hNm
    rw [htot] at hres
    exact hres.congr_fun (fun k => (hfold k).symm)
  -- ## Step 0 (continued): the radial energy is finite, by the lower half of (27)
  have hcinorm : ∀ (s θ : ℝ), 0 ≤ s →
      ‖((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = s := by
    intro s θ hs
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs]
  have hcimem : ∀ (s θ : ℝ), 0 < s → s < 1 →
      ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro s θ hs hs1
    show ‖_‖ < 1
    rw [hcinorm s θ hs.le]
    exact hs1
  have hBdmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} := hBopen.measurableSet
  have hFFmeas : Measurable (fun ζ : ℂ =>
      Set.indicator {ξ : ℂ | ‖ξ‖ < 1} (fun ξ => ENNReal.ofReal (‖HRad H ξ‖ ^ 2)) ζ) := by
    refine Measurable.indicator ?_ hBdmeas
    exact ENNReal.measurable_ofReal.comp ((hRadmeas.norm).pow_const 2)
  have hcK : (0 : ℝ) < 1 + (K ^ 2)⁻¹ := by positivity
  have hFFfin : (∫⁻ ζ : ℂ,
      Set.indicator {ξ : ℂ | ‖ξ‖ < 1} (fun ξ => ENNReal.ofReal (‖HRad H ξ‖ ^ 2)) ζ) < ⊤ := by
    have h27 := QCDistortionPolar K {ξ : ℂ | ‖ξ‖ < 1} H hBopen hK hdiff hqr
    have hne0 : ∀ᵐ ζ : ℂ, ζ ≠ 0 := by
      refine (MeasureTheory.ae_iff).mpr ?_
      simp
    have hdom : ∀ᵐ ζ : ℂ,
        Set.indicator {ξ : ℂ | ‖ξ‖ < 1} (fun ξ => ENNReal.ofReal (‖HRad H ξ‖ ^ 2)) ζ
          ≤ ENNReal.ofReal (2 / (1 + (K ^ 2)⁻¹))
            * Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
                (fun ξ => ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) ζ := by
      filter_upwards [h27, hne0] with ζ h1 h2
      by_cases hz : ζ ∈ {ξ : ℂ | ‖ξ‖ < 1}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 := (h1 hz h2).2.1
        rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
        nlinarith [h3]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hdom) ?_
    rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (2 / (1 + (K ^ 2)⁻¹)) ≠ ⊤)]
    refine ENNReal.mul_lt_top (by simp) ?_
    rw [MeasureTheory.lintegral_indicator hBdmeas]
    have hfi := hint.2
    rw [MeasureTheory.HasFiniteIntegral] at hfi
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hfi
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    rw [Real.enorm_eq_ofReal (by positivity)]
  -- the polar change of variables, with the angular window `(0, 2π)`
  obtain ⟨FF, hFFval⟩ : ∃ G : ℂ → ENNReal, ∀ ζ : ℂ,
      G ζ = Set.indicator {ξ : ℂ | ‖ξ‖ < 1} (fun ξ => ENNReal.ofReal (‖HRad H ξ‖ ^ 2)) ζ :=
    ⟨_, fun _ => rfl⟩
  have hFFfun : FF = fun ζ => Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
      (fun ξ => ENNReal.ofReal (‖HRad H ξ‖ ^ 2)) ζ := funext hFFval
  have hFFm : Measurable FF := by rw [hFFfun]; exact hFFmeas
  have hFFf : (∫⁻ ζ : ℂ, FF ζ) < ⊤ := by rw [hFFfun]; exact hFFfin
  have hcisymm : ∀ q : ℝ × ℝ, (Complex.polarCoord.symm q)
      = ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)) := by
    intro q
    rw [Complex.polarCoord_symm_apply]
    simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hrot : ∀ (s θ : ℝ), -((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = ((s : ℂ) * Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I)) := by
    intro s θ
    rw [show (((θ + Real.pi : ℝ) : ℂ)) * Complex.I
        = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hcicont : Continuous
      (fun q : ℝ × ℝ => ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))) := by fun_prop
  have hpol := Complex.lintegral_comp_polarCoord_symm (fun ζ => FF (-ζ))
  rw [MeasureTheory.lintegral_neg_eq_self FF,
    show (polarCoord.target : Set (ℝ × ℝ))
      = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl] at hpol
  simp only [hcisymm, smul_eq_mul] at hpol
  have hmeas2 : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal q.1 * FF (-((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hFFm.comp (continuous_neg.measurable.comp hcicont.measurable))
  have hton : (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * FF (-((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.lintegral_prod _ hmeas2.aemeasurable
  have hmemsh : ∀ θ : ℝ,
      (θ ∈ Set.Ioo (-Real.pi) Real.pi ↔ θ + Real.pi ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
    intro θ
    constructor
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have htr : ∀ r : ℝ, (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
        FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro r
    have h1 : ∀ θ : ℝ, Set.indicator (Set.Ioo (-Real.pi) Real.pi)
          (fun θ => FF (-((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) θ
        = Set.indicator (Set.Ioo (0 : ℝ) (2 * Real.pi))
          (fun θ => FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (θ + Real.pi) := by
      intro θ
      by_cases h : θ ∈ Set.Ioo (-Real.pi) Real.pi
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmemsh θ).mp h), hrot]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun hc => h ((hmemsh θ).mpr hc))]
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioo,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioo,
      MeasureTheory.lintegral_congr h1]
    exact MeasureTheory.lintegral_add_right_eq_self
      (Set.indicator (Set.Ioo (0 : ℝ) (2 * Real.pi))
        (fun θ => FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) Real.pi
  have hub : (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r
        * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)) < ⊤ := by
    have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r
          * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        = ∫⁻ ζ : ℂ, FF ζ := by
      rw [← hpol, hton]
      refine MeasureTheory.lintegral_congr (fun r => ?_)
      rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal r ≠ ⊤), htr r]
    have hle : (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r
          * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
              ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r
          * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
      refine le_trans (le_of_eq ?_)
        (MeasureTheory.lintegral_mono_set
          (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) from fun x hx => hx.1))
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
      congr 1
      refine MeasureTheory.lintegral_congr (fun θ => ?_)
      rw [hFFval, Set.indicator_of_mem (hcimem r θ hr.1 hr.2)]
    refine lt_of_le_of_lt hle ?_
    rw [hstep]
    exact hFFf
  -- the same polar computation as an identity, for Steps 4 and 5
  have hFFpol : (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r
        * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
      = ∫⁻ ζ : ℂ, FF ζ := by
    have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r
          * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        = ∫⁻ ζ : ℂ, FF ζ := by
      rw [← hpol, hton]
      refine MeasureTheory.lintegral_congr (fun r => ?_)
      rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal r ≠ ⊤), htr r]
    rw [← hstep, ← MeasureTheory.lintegral_indicator measurableSet_Ioo,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioi]
    refine MeasureTheory.lintegral_congr (fun r => ?_)
    by_cases h1 : r ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ioi.mpr h1.1)]
      congr 1
      refine MeasureTheory.lintegral_congr (fun θ => ?_)
      rw [hFFval, Set.indicator_of_mem (hcimem r θ h1.1 h1.2)]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : r ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem h2]
        have hr0 : (0 : ℝ) < r := h2
        have hr1 : (1 : ℝ) ≤ r := by
          rcases lt_or_ge r 1 with h | h
          · exact absurd (Set.mem_Ioo.mpr ⟨hr0, h⟩) h1
          · exact h
        have hzfun : ∀ θ : ℝ, FF ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
          intro θ
          have hnm : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ∉ {ξ : ℂ | ‖ξ‖ < 1} := by
            intro hc
            have hcc : ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ < 1 := hc
            rw [hcinorm r θ hr0.le] at hcc
            linarith
          rw [hFFval, Set.indicator_of_notMem hnm]
        rw [MeasureTheory.lintegral_congr hzfun, MeasureTheory.lintegral_zero, mul_zero]
      · rw [Set.indicator_of_notMem h2]
  -- ## Step 3: integration in `r`
  have hmeasr : Measurable (fun r : ℝ => ENNReal.ofReal r
      * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.mul ?_
    have h1 : Measurable (fun q : ℝ × ℝ =>
        ENNReal.ofReal (‖HRad H ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((hRadmeas.comp hcicont.measurable).norm).pow_const 2)
    exact h1.lintegral_prod_right'
  have hF0'' : ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      ((∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)) < ⊤ ∧
        IntegrableOn
          (fun θ : ℝ => ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
          (Set.Ioc (0 : ℝ) (2 * Real.pi)) volume) := by
    have hae := MeasureTheory.ae_lt_top hmeasr (ne_of_lt hub)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae
    filter_upwards [hae] with r hr hrmem
    have hfin := hr hrmem
    have hrne : ENNReal.ofReal r ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hrmem.1
    have hLLfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)) < ⊤ := by
      rcases lt_or_ge (∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)) ⊤
        with h | h
      · exact h
      · rw [top_le_iff] at h
        rw [h, ENNReal.mul_top hrne] at hfin
        exact absurd hfin (by simp)
    refine ⟨hLLfin, ?_⟩
    have hIoo : IntegrableOn
        (fun θ : ℝ => ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        (Set.Ioo (0 : ℝ) (2 * Real.pi)) volume := by
      refine ⟨((hRadmeas.comp (hcimeas r)).norm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.HasFiniteIntegral]
      refine lt_of_le_of_lt (le_of_eq ?_) hLLfin
      exact MeasureTheory.lintegral_congr
        (fun θ => Real.enorm_eq_ofReal (by positivity))
    exact hIoo.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc).symm
  -- `λ_k > 0` for `k ≥ n + 1`, by (25)
  have hlampos : ∀ k : ℕ, 0 < LambdaCoef n (n + 1 + k) p := by
    intro k
    have h := ((LambdaEpsEstimates n p hn hp).2.2.2 (n + 1 + k) (by omega)).1
    have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := by
      have hnp : (0 : ℝ) < (n : ℝ) * p := by positivity
      exact div_pos hp1 hnp
    linarith
  -- the radius-wise identity, in `ENNReal`
  have hrad : ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      ENNReal.ofReal r * (∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
        = ∑' k : ℕ, ENNReal.ofReal (r * (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)))) := by
    filter_upwards [hstep2, hF0''] with r h2r h0r hrmem
    obtain ⟨hLLfin, hIoc⟩ := h0r hrmem
    have hr0 : (0 : ℝ) < r := hrmem.1
    have hsum := h2r hrmem hIoc
    have hconv : ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        = ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) := by
      rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc
          (Filter.Eventually.of_forall (fun θ => by positivity)),
        ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
    rw [← hconv, ← hsum.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum.summable,
      ← ENNReal.tsum_mul_left]
    exact tsum_congr (fun k => (ENNReal.ofReal_mul hr0.le).symm)
  -- the term-by-term radial integral
  have hterm : ∀ k : ℕ, (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (r * (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)))))
      = ENNReal.ofReal (Real.pi * (LambdaCoef n (n + 1 + k) p
          * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
    intro k
    have hlamk := hlampos k
    have hc0 : (0 : ℝ) ≤ 2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by positivity
    have hint1 : IntervalIntegrable
        (fun r : ℝ => r ^ (2 * LambdaCoef n (n + 1 + k) p - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hval : (∫ r in (0 : ℝ)..1, r ^ (2 * LambdaCoef n (n + 1 + k) p - 1))
        = 1 / (2 * LambdaCoef n (n + 1 + k) p) := by
      rw [integral_rpow (Or.inl (by linarith)),
        show 2 * LambdaCoef n (n + 1 + k) p - 1 + 1
          = 2 * LambdaCoef n (n + 1 + k) p from by ring,
        Real.one_rpow, Real.zero_rpow (by positivity)]
      ring
    have hcong : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (r * (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2))))
          = ENNReal.ofReal ((2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
              * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
            * r ^ (2 * LambdaCoef n (n + 1 + k) p - 1)) := by
      intro r hr
      congr 1
      have hrr : r * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)
          = r ^ (2 * LambdaCoef n (n + 1 + k) p - 1) := by
        rw [show (2 * LambdaCoef n (n + 1 + k) p - 1)
            = (2 * LambdaCoef n (n + 1 + k) p - 2) + 1 from by ring,
          Real.rpow_add hr.1, Real.rpow_one]
        ring
      calc r * (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
              * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
              * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)))
          = (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
              * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
            * (r * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2)) := by ring
        _ = _ := by rw [hrr]
    have hIint : IntegrableOn
        (fun r : ℝ => (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
          * r ^ (2 * LambdaCoef n (n + 1 + k) p - 1)) (Set.Ioc (0 : ℝ) 1) volume := by
      have h := hint1.const_mul (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
      exact h
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hcong,
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIint
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun r hr => by
            have := hr.1
            positivity))),
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, hval]
    congr 1
    field_simp
  -- the measurability of each radial term
  have hmeask : ∀ k : ℕ, Measurable (fun r : ℝ =>
      ENNReal.ofReal (r * (2 * Real.pi * (LambdaCoef n (n + 1 + k) p ^ 2
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2
        * r ^ (2 * LambdaCoef n (n + 1 + k) p - 2))))) := by
    intro k
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_id.mul
      (((measurable_id.pow measurable_const).const_mul _).const_mul _)
  have hmain : (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r
        * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
      = ∑' k : ℕ, ENNReal.ofReal (Real.pi * (LambdaCoef n (n + 1 + k) p
          * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
    rw [MeasureTheory.lintegral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr hrad),
      MeasureTheory.lintegral_tsum (fun k => (hmeask k).aemeasurable)]
    exact tsum_congr hterm
  have hmainfin : (∑' k : ℕ, ENNReal.ofReal (Real.pi * (LambdaCoef n (n + 1 + k) p
      * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))) ≠ ⊤ := by
    rw [← hmain]
    exact ne_of_lt hub
  have hSS0 : ∀ k : ℕ, 0 ≤ Real.pi * (LambdaCoef n (n + 1 + k) p
      * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by
    intro k
    have hl := (hlampos k).le
    positivity
  have hsumSS : Summable (fun k : ℕ => Real.pi * (LambdaCoef n (n + 1 + k) p
      * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
    have h := ENNReal.summable_toReal hmainfin
    refine h.congr (fun k => ?_)
    rw [ENNReal.toReal_ofReal (hSS0 k)]
  have hsum1 : Summable (fun k : ℕ => LambdaCoef n (n + 1 + k) p
      * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by
    have h : Summable (fun k : ℕ => Real.pi * (LambdaCoef n (n + 1 + k) p
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := hsumSS
    exact (summable_mul_left_iff (ne_of_gt hpi)).mp h
  -- the left-hand side of (E)
  have hIInn : ∀ r : ℝ, 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 :=
    fun r => intervalIntegral.integral_nonneg (by positivity) (fun u _ => by positivity)
  have hconv2 : ∀ᵐ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
      ENNReal.ofReal (r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        = ENNReal.ofReal r * ∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) := by
    filter_upwards [hF0''] with r h0r hrmem
    obtain ⟨hLLfin, hIoc⟩ := h0r hrmem
    rw [ENNReal.ofReal_mul hrmem.1.le]
    congr 1
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc
        (Filter.Eventually.of_forall (fun θ => by positivity)),
      ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
  have hIIsm : MeasureTheory.StronglyMeasurable (fun r : ℝ =>
      ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
        ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) := by
    have h1 : MeasureTheory.StronglyMeasurable (fun q : ℝ × ℝ =>
        ‖HRad H ((q.1 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I))‖ ^ 2) :=
      (((hRadmeas.comp hcicont.measurable).norm).pow_const 2).stronglyMeasurable
    exact h1.integral_prod_right'
  have hgint : IntegrableOn (fun r : ℝ => r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
      (Set.Ioc (0 : ℝ) 1) volume := by
    refine ⟨?_, ?_⟩
    · have heq : (fun r : ℝ => r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
          = fun r : ℝ => r * ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
            ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 := by
        funext r
        rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      rw [heq]
      exact (measurable_id.stronglyMeasurable.mul hIIsm).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_enorm,
        ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
      refine lt_of_le_of_lt (le_of_eq ?_) hub
      refine MeasureTheory.lintegral_congr_ae ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr ?_
      filter_upwards [hconv2] with r hcr hrmem
      rw [Real.enorm_eq_ofReal (mul_nonneg hrmem.1.le (hIInn r)), hcr hrmem]
  have hLHS : ENNReal.ofReal (∫ r in (0 : ℝ)..1, r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
      = ∑' k : ℕ, ENNReal.ofReal (Real.pi * (LambdaCoef n (n + 1 + k) p
          * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun r hr => mul_nonneg hr.1.le (hIInn r)))),
      ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      MeasureTheory.lintegral_congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr hconv2)]
    exact hmain
  -- ## Step 4 preparation: the linear-weight summability, by comparison with (1)
  have hnne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hγne : GammaExp n p ≠ 0 := ne_of_gt hγ
  have hc0 : (0 : ℝ) < ((n : ℝ) + 1) / GammaExp n p := by positivity
  have hbd3 : ∀ m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
      ≤ (((n : ℝ) + 1) / GammaExp n p) * (LambdaCoef n (n + 1 + m) p
        * (1 + EpsCoef n (n + 1 + m) p ^ 2) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by
    intro m
    have hlam := LambdaLinearLowerBound n p hn hp (n + 1 + m) (by omega)
    have hcast : ((n + 1 + m : ℕ) : ℝ) = (n : ℝ) + 1 + (m : ℝ) := by push_cast; ring
    rw [hcast] at hlam
    have h1 : ((n : ℝ) + 1 + (m : ℝ))
        ≤ (((n : ℝ) + 1) / GammaExp n p) * LambdaCoef n (n + 1 + m) p := by
      have h2 := mul_le_mul_of_nonneg_left hlam hc0.le
      refine le_trans (le_of_eq ?_) h2
      field_simp
    have hA : (0 : ℝ) ≤ ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by positivity
    have hlk := (hlampos m).le
    have he : (1 : ℝ) ≤ 1 + EpsCoef n (n + 1 + m) p ^ 2 := by
      nlinarith [sq_nonneg (EpsCoef n (n + 1 + m) p)]
    refine le_trans (mul_le_mul_of_nonneg_right h1 hA) ?_
    have hstep : LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
        ≤ LambdaCoef n (n + 1 + m) p * (1 + EpsCoef n (n + 1 + m) p ^ 2)
          * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by
      nlinarith [mul_nonneg hlk hA]
    calc (((n : ℝ) + 1) / GammaExp n p) * LambdaCoef n (n + 1 + m) p
          * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
        = (((n : ℝ) + 1) / GammaExp n p)
            * (LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstep hc0.le
  have hsum3 : Summable (fun m : ℕ =>
      ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) hbd3 (hsum1.mul_left _)
    positivity
  have hTnn : (0 : ℝ) ≤ ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
      * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by
    refine tsum_nonneg (fun k => ?_)
    have hl := (hlampos k).le
    positivity
  have hSnn : (0 : ℝ) ≤ ∑' m : ℕ,
      ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 :=
    tsum_nonneg (fun m => by positivity)
  -- the Fourier side of the energy, as a single `ENNReal`
  have hT : ENNReal.ofReal (Real.pi * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
      = ∫⁻ ζ : ℂ, FF ζ := by
    rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hSS0 hsumSS, ← hmain]
    exact hFFpol
  -- the Dirichlet side of the energy, as a single `ENNReal`
  have hgnn : ∀ ξ : ℂ, (0 : ℝ) ≤ ‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2 := fun ξ => by positivity
  have hU : ENNReal.ofReal (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2))
      = ∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hgnn)
  have hUnn : (0 : ℝ) ≤ ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2) :=
    MeasureTheory.setIntegral_nonneg hBdmeas (fun x _ => hgnn x)
  -- the two halves of (27), integrated over the disc
  have h27' := QCDistortionPolar K {ξ : ℂ | ‖ξ‖ < 1} H hBopen hK hdiff hqr
  have hne0' : ∀ᵐ ζ : ℂ, ζ ≠ 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    simp
  have hFFle : (∫⁻ ζ : ℂ, FF ζ)
      ≤ ENNReal.ofReal (2 / (1 + (K ^ 2)⁻¹))
        * ∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2) := by
    have hdom : ∀ᵐ ζ : ℂ, FF ζ ≤ ENNReal.ofReal (2 / (1 + (K ^ 2)⁻¹))
        * Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
            (fun ξ => ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) ζ := by
      filter_upwards [h27', hne0'] with ζ h1 h2
      rw [hFFval]
      by_cases hz : ζ ∈ {ξ : ℂ | ‖ξ‖ < 1}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 := (h1 hz h2).2.1
        rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
        nlinarith [h3]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    refine le_trans (MeasureTheory.lintegral_mono_ae hdom) (le_of_eq ?_)
    rw [MeasureTheory.lintegral_const_mul' _ _
        (by simp : ENNReal.ofReal (2 / (1 + (K ^ 2)⁻¹)) ≠ ⊤),
      MeasureTheory.lintegral_indicator hBdmeas]
  have hGGle : (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2))
      ≤ ENNReal.ofReal ((1 + K ^ 2) / 2) * ∫⁻ ζ : ℂ, FF ζ := by
    have hdom : ∀ᵐ ζ : ℂ, Set.indicator {ξ : ℂ | ‖ξ‖ < 1}
          (fun ξ => ENNReal.ofReal (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) ζ
        ≤ ENNReal.ofReal ((1 + K ^ 2) / 2) * FF ζ := by
      filter_upwards [h27', hne0'] with ζ h1 h2
      rw [hFFval]
      by_cases hz : ζ ∈ {ξ : ℂ | ‖ξ‖ < 1}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 := (h1 hz h2).2.2
        nlinarith [h3]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    rw [← MeasureTheory.lintegral_indicator hBdmeas]
    refine le_trans (MeasureTheory.lintegral_mono_ae hdom) (le_of_eq ?_)
    rw [MeasureTheory.lintegral_const_mul' _ _
      (by simp : ENNReal.ofReal ((1 + K ^ 2) / 2) ≠ ⊤)]
  have hreal1 : Real.pi * (∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
        * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
      ≤ 2 / (1 + (K ^ 2)⁻¹)
        * ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2) := by
    have h := hFFle
    rw [← hT, ← hU, ← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hUnn)).mp h
  have hreal2 : (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2))
      ≤ (1 + K ^ 2) / 2 * (Real.pi * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
          * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
    have h := hGGle
    rw [← hT, ← hU, ← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (mul_nonneg hpi.le hTnn))).mp h
  refine ⟨hsum1, ?_, hsum3, ?_, ?_⟩
  · -- ## the energy identity (E)
    have hnn1 : 0 ≤ ∫ r in (0 : ℝ)..1, r * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖HRad H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun u hu => mul_nonneg hu.1 (hIInn u))
    refine (ENNReal.ofReal_eq_ofReal_iff hnn1 (by positivity)).mp ?_
    rw [hLHS, ← ENNReal.ofReal_tsum_of_nonneg hSS0 hsumSS, tsum_mul_left]
  · -- ## Step 4: the coefficient bound (22), lower direction
    have hS4 : (∑' m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2)
        ≤ (((n : ℝ) + 1) / GammaExp n p) * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum hbd3 hsum3 (hsum1.mul_left _)
    refine le_trans hS4
      (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hUnn))
    rw [hC1def]
    have hcc : (0 : ℝ) < ((n : ℝ) + 1) / (GammaExp n p * Real.pi) := by positivity
    have hinv : (K⁻¹ : ℝ) ^ 2 = (K ^ 2)⁻¹ := by rw [inv_pow]
    have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK0
    have hcKne : (1 : ℝ) + (K ^ 2)⁻¹ ≠ 0 := ne_of_gt hcK
    calc (((n : ℝ) + 1) / GammaExp n p) * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)
        = ((n : ℝ) + 1) / (GammaExp n p * Real.pi)
            * (Real.pi * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
              * (1 + EpsCoef n (n + 1 + k) p ^ 2)
                * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2)) := by
          field_simp
      _ ≤ ((n : ℝ) + 1) / (GammaExp n p * Real.pi)
            * (2 / (1 + (K ^ 2)⁻¹)
              * ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hreal1 hcc.le
      _ = 2 * ((n : ℝ) + 1) / (Real.pi * GammaExp n p * (1 + K⁻¹ ^ 2))
            * ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2) := by
          rw [hinv]
          field_simp
  · -- ## Step 5: the coefficient bound (22), upper direction
    have hbd5 : ∀ m : ℕ, LambdaCoef n (n + 1 + m) p
        * (1 + EpsCoef n (n + 1 + m) p ^ 2) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
      ≤ 2 * Real.sqrt (p - 1)
          * (((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by
      intro m
      have hlamle := ((LambdaEpsEstimates n p hn hp).2.2.2 (n + 1 + m) (by omega)).2
      have heps := (LambdaEpsEstimates n p hn hp).2.2.1 (n + 1 + m) (by omega)
      have hcast : ((n + 1 + m : ℕ) : ℝ) = (n : ℝ) + 1 + (m : ℝ) := by push_cast; ring
      rw [hcast] at hlamle
      have hA : (0 : ℝ) ≤ ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by positivity
      have hlk := (hlampos m).le
      have he2 : EpsCoef n (n + 1 + m) p ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (EpsCoef n (n + 1 + m) p), sq_abs (EpsCoef n (n + 1 + m) p)]
      have he3 : (1 : ℝ) + EpsCoef n (n + 1 + m) p ^ 2 ≤ 2 := by linarith
      have hprod : (0 : ℝ) ≤ LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 :=
        mul_nonneg hlk hA
      have hstep2 : LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
          ≤ (((n : ℝ) + 1 + (m : ℝ)) * Real.sqrt (p - 1))
            * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hlamle hA
      have s1 : LambdaCoef n (n + 1 + m) p * (1 + EpsCoef n (n + 1 + m) p ^ 2)
            * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
          ≤ LambdaCoef n (n + 1 + m) p * 2 * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by
        calc LambdaCoef n (n + 1 + m) p * (1 + EpsCoef n (n + 1 + m) p ^ 2)
              * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
            = (LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2)
                * (1 + EpsCoef n (n + 1 + m) p ^ 2) := by ring
          _ ≤ (LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) * 2 :=
              mul_le_mul_of_nonneg_left he3 hprod
          _ = LambdaCoef n (n + 1 + m) p * 2
                * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by ring
      have s2 : LambdaCoef n (n + 1 + m) p * 2 * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
          ≤ 2 * Real.sqrt (p - 1)
            * (((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by
        calc LambdaCoef n (n + 1 + m) p * 2 * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
            = 2 * (LambdaCoef n (n + 1 + m) p * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by ring
          _ ≤ 2 * ((((n : ℝ) + 1 + (m : ℝ)) * Real.sqrt (p - 1))
                * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hstep2 (by norm_num)
          _ = 2 * Real.sqrt (p - 1)
                * (((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) := by ring
      exact le_trans s1 s2
    have hT5 : (∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
          * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
        ≤ 2 * Real.sqrt (p - 1) * ∑' m : ℕ,
            ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum hbd5 hsum1 (hsum3.mul_left _)
    refine le_trans hreal2
      (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hSnn))
    rw [hC2def]
    have hcc : (0 : ℝ) < (1 + K ^ 2) / 2 * Real.pi := by positivity
    calc (1 + K ^ 2) / 2 * (Real.pi * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
            * (1 + EpsCoef n (n + 1 + k) p ^ 2) * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2))
        = (1 + K ^ 2) / 2 * Real.pi * ∑' k : ℕ, (LambdaCoef n (n + 1 + k) p
            * (1 + EpsCoef n (n + 1 + k) p ^ 2)
              * ‖A ((n : ℤ) + 1 + (k : ℤ))‖ ^ 2) := by ring
      _ ≤ (1 + K ^ 2) / 2 * Real.pi * (2 * Real.sqrt (p - 1) * ∑' m : ℕ,
            ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hT5 hcc.le
      _ = (1 + K ^ 2) * Real.pi * Real.sqrt (p - 1) * ∑' m : ℕ,
            ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by ring
