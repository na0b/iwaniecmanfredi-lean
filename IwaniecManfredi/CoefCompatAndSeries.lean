import IwaniecManfredi.FourierCoefForm36
import IwaniecManfredi.FourierCoefOde
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.LambdaEpsEstimates
import IwaniecManfredi.Thm2Term

/-- The compatibility conditions (38) and (39) of the paper, the corner
`A_{-n} = 0`, and the series (40) together with its identification with (19).
The second form of `ε_k` is a polynomial consequence of the indicial equation
alone -- no square root is unfolded.  No hypothesis `p ≠ 2` is needed: both
`A_{-n} = 0` and (39) are read off the instance of (38) at the index `-k`,
whose coefficient `2λ_k + p(n+k)` is positive for every `1 < p < ∞`. -/
theorem CoefCompatAndSeries (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (H : ℂ → ℂ) (hc : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1})
    (hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H)
    (hdiff : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ)
    (h18 : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H)
    (A : ℤ → ℂ)
    (hA : ∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)) :
    (∀ k : ℤ, (n : ℤ) ≤ |k| →
      ((2 * LambdaCoef n k.natAbs p + p * ((n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * A k
        = ((2 - p : ℝ) : ℂ) * (((n : ℝ) + (k : ℝ) : ℝ) : ℂ) * starRingEnd ℂ (A (-k))) ∧
    A (-(n : ℤ)) = 0 ∧
    (∀ k : ℤ, (n : ℤ) < k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k)) ∧
    (∀ k : ℕ, n ≤ k → ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (A (k : ℤ) * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)
            + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                * Complex.exp (-((k : ℂ) * (θ : ℂ)) * Complex.I))
          * ((r ^ LambdaCoef n k p : ℝ) : ℂ)
          * Complex.exp (-((n : ℂ) * (θ : ℂ)) * Complex.I)) ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto
        (fun N : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - ∑ k ∈ Finset.Icc n (n + N),
                Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        Filter.atTop (nhds 0)) := by
  -- ## Step 0: the indicial equation (I).  This is the ONLY property of `λ` used
  -- below: the square root of (37) is squared away once and never unfolded again.
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hI : ∀ k : ℕ, LambdaCoef n k p ^ 2 + p * (n : ℝ) * LambdaCoef n k p
      + ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) = 0 := by
    intro k
    have hR : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      positivity
    have hsq : Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) ^ 2
        = 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := Real.sq_sqrt hR
    rw [LambdaCoef]
    linear_combination hsq / 4
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  obtain ⟨hode1, hode2, hsm⟩ := FourierCoefOde n p hn hp H hc hw hdiff h18
  -- ## Step 1: conjunct (1) = (38).  On the open interval `Ioo 0 1` the hypothesis
  -- `hA` is an `EventuallyEq`, so it may be differentiated.
  have hderiv : ∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      deriv (FourierCoefOfH n H k) r
        = A k * ((LambdaCoef n k.natAbs p : ℝ) : ℂ)
            * ((r ^ (LambdaCoef n k.natAbs p - 1) : ℝ) : ℂ) := by
    intro k hk r hr
    have heq : FourierCoefOfH n H k
        =ᶠ[nhds r] fun s : ℝ => A k * ((s ^ LambdaCoef n k.natAbs p : ℝ) : ℂ) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => hA k hk s hs)
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun s : ℝ => (s ^ LambdaCoef n k.natAbs p : ℝ))
        (LambdaCoef n k.natAbs p * r ^ (LambdaCoef n k.natAbs p - 1)) r :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hr.1))
    rw [((hd.ofReal_comp).const_mul (A k)).deriv]
    push_cast
    ring
  have h38 : ∀ k : ℤ, (n : ℤ) ≤ |k| →
      ((2 * LambdaCoef n k.natAbs p + p * ((n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * A k
        = ((2 - p : ℝ) : ℂ) * (((n : ℝ) + (k : ℝ) : ℝ) : ℂ) * starRingEnd ℂ (A (-k)) := by
    intro k hk
    have hr : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hkk : (n : ℤ) ≤ |(-k)| := by
      rw [abs_neg]
      exact hk
    have hnat : (-k).natAbs = k.natAbs := Int.natAbs_neg k
    have hhalf : ((1 / 2 : ℝ) ^ (LambdaCoef n k.natAbs p - 1) : ℝ)
        = 2 * ((1 / 2 : ℝ) ^ (LambdaCoef n k.natAbs p) : ℝ) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      ring
    have h1 := hode1 k (1 / 2) hr
    rw [hderiv k hk (1 / 2) hr, hA k hk (1 / 2) hr, hA (-k) hkk (1 / 2) hr, hnat,
      hhalf, map_mul, Complex.conj_ofReal] at h1
    have hpwC : (((1 / 2 : ℝ) ^ (LambdaCoef n k.natAbs p) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
    refine mul_right_cancel₀ hpwC ?_
    push_cast at h1 ⊢
    linear_combination h1
  -- ## Step 2: conjunct (2).  Read off (38) AT `-n`, whose coefficient
  -- `2λ_n + p(n+n) = 2pn` is positive for every `1 < p < ∞`; dividing by `(2-p)`,
  -- as the paper does at (39), would force `p ≠ 2`.
  have hAn : A (-(n : ℤ)) = 0 := by
    have hk : (n : ℤ) ≤ |(-(n : ℤ))| := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ))]
    have hnat : ((-(n : ℤ))).natAbs = n := by simp
    have h := h38 (-(n : ℤ)) hk
    rw [hnat, hlamn, neg_neg] at h
    have hzero : ((2 - p : ℝ) : ℂ) * (((n : ℝ) + ((-(n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
        * starRingEnd ℂ (A (n : ℤ)) = 0 := by
      have he : (((n : ℝ) + ((-(n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) = 0 := by
        push_cast
        ring
      rw [he]
      ring
    rw [hzero] at h
    have hcoef : ((2 * (0 : ℝ) + p * ((n : ℝ) - ((-(n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      have he : 2 * (0 : ℝ) + p * ((n : ℝ) - ((-(n : ℤ) : ℤ) : ℝ)) = 2 * p * (n : ℝ) := by
        push_cast
        ring
      rw [he]
      have hp2 : (0 : ℝ) < p := by linarith
      positivity
    exact (mul_eq_zero.mp h).resolve_left hcoef
  -- ## Step 3: conjunct (3) = (39), again from (38) at `-k`.  After clearing the two
  -- positive denominators the scalar identity is twice the indicial equation.
  have h39 : ∀ k : ℤ, (n : ℤ) < k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k) := by
    intro k hk
    have hk0 : (0 : ℤ) < k := by omega
    have hkabs : (n : ℤ) ≤ |(-k)| := by
      rw [abs_neg, abs_of_pos hk0]
      omega
    have hnat : (-k).natAbs = k.natAbs := Int.natAbs_neg k
    have hnatk : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg (le_of_lt hk0)
    have hkr : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have he : (((k.natAbs : ℕ) : ℤ) : ℝ) = (k : ℝ) := by
        rw [hnatk]
      simpa using he
    have hkn : (n : ℝ) + 1 ≤ (k : ℝ) := by
      have hh : (n : ℤ) + 1 ≤ k := by omega
      exact_mod_cast hh
    have hlam0 : 0 ≤ LambdaCoef n k.natAbs p := by
      have hge : n + 1 ≤ k.natAbs := by omega
      have h1 := (hlambd k.natAbs hge).1
      have hp2 : (0 : ℝ) < p := by linarith
      have hnp : (0 : ℝ) < (n : ℝ) * p := by positivity
      have h2 : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos hp0 hnp
      linarith
    have hIk : LambdaCoef n k.natAbs p ^ 2 + p * (n : ℝ) * LambdaCoef n k.natAbs p
        + ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) = 0 := by
      have hh := hI k.natAbs
      rw [hkr] at hh
      exact hh
    have hd1 : LambdaCoef n k.natAbs p + (n : ℝ) + (k : ℝ) ≠ 0 := by
      refine ne_of_gt ?_
      linarith
    have hd2 : 2 * LambdaCoef n k.natAbs p + p * ((n : ℝ) + (k : ℝ)) ≠ 0 := by
      refine ne_of_gt ?_
      have hp2 : (0 : ℝ) < p := by linarith
      have h2 : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by linarith
      have h3 : (0 : ℝ) < p * ((n : ℝ) + (k : ℝ)) := by positivity
      linarith
    have hd2C : ((2 * LambdaCoef n k.natAbs p + p * ((n : ℝ) + (k : ℝ)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hd2
    have hscalar : EpsCoef n k.natAbs p
        = (2 - p) * ((n : ℝ) - (k : ℝ))
            / (2 * LambdaCoef n k.natAbs p + p * ((n : ℝ) + (k : ℝ))) := by
      rw [EpsCoef, hkr, div_eq_div_iff hd1 hd2]
      linear_combination 2 * hIk
    have h := h38 (-k) hkabs
    rw [hnat, neg_neg] at h
    rw [hscalar, Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hd2C]
    push_cast at h ⊢
    linear_combination h
  -- ## Step 4: conjunct (4), the polar form of a single summand of (19).
  have h40 : ∀ k : ℕ, n ≤ k → ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (A (k : ℤ) * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)
            + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                * Complex.exp (-((k : ℂ) * (θ : ℂ)) * Complex.I))
          * ((r ^ LambdaCoef n k p : ℝ) : ℂ)
          * Complex.exp (-((n : ℂ) * (θ : ℂ)) * Complex.I) := by
    intro k hk r hr θ
    have hnorm : ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    have hconjE : starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))
        = Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I]
    have hconjxi : starRingEnd ℂ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (r : ℂ) * starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) := by
      rw [map_mul, Complex.conj_ofReal]
    have hrcomb : ((r : ℂ)) ^ k * ((r ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
          * ((r : ℂ)) ^ (-(n : ℤ))
        = ((r ^ LambdaCoef n k p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_zpow, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul]
      congr 1
      rw [← Real.rpow_natCast r k, ← Real.rpow_intCast r (-(n : ℤ)),
        ← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      push_cast
      ring
    have he1 : Complex.exp ((θ : ℂ) * Complex.I) ^ k
        = Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    have he2 : (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ k
        = Complex.exp (-((k : ℂ) * (θ : ℂ)) * Complex.I) := by
      rw [hconjE, ← Complex.exp_nat_mul]
      congr 1
      ring
    have he3 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ))
        = Complex.exp (-((n : ℂ) * (θ : ℂ)) * Complex.I) := by
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    simp only [Thm2Term, hnorm, hconjxi, mul_pow, mul_zpow]
    rw [he1, he2, he3, ← hrcomb]
    ring
  refine ⟨h38, hAn, h39, h40, ?_⟩
  -- ## Step 5: conjunct (5), the circlewise `L²` convergence.  Part (f) of
  -- `FourierCoefRegularity` supplies it for the SYMMETRIC cutoff `|j| ≤ M`; the
  -- reindexing `M = n + N` and the fold `j ↔ -j` turn that sum into the partial sum
  -- of (19).  No completeness of the trigonometric system is used.
  obtain ⟨hacont, -, -, -, -, hfreg⟩ := FourierCoefRegularity n H hc hw hdiff
  intro r hr
  have hr' : r ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hr.1, hr.2⟩
  -- the low coefficients vanish: the first case of (36)
  have hlow : ∀ j : ℤ, j.natAbs < n → FourierCoefOfH n H j r = 0 := fun j hj =>
    (FourierCoefForm36 n p j hn hp (FourierCoefOfH n H j) (hacont j) (hsm j)
      (fun s hs => hode2 j s hs)).1 hj r hr'
  -- `A_{-k} = ε_k conj(A_k)` for every `k ≥ n`, the corner `k = n` included
  have hAneg : ∀ k : ℕ, n ≤ k →
      A (-(k : ℤ)) = ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)) := by
    intro k hk
    rcases eq_or_lt_of_le hk with heq | hlt
    · rw [← heq, hAn, hepsn]
      simp
    · have h := h39 (k : ℤ) (by exact_mod_cast hlt)
      rwa [Int.natAbs_natCast] at h
  -- the fold: the `j = k` and `j = -k` terms of the symmetric sum add up to `T_k`
  have hpair : ∀ k : ℕ, n ≤ k → ∀ θ : ℝ,
      FourierCoefOfH n H (k : ℤ) r
            * Complex.exp (((((k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + FourierCoefOfH n H (-(k : ℤ)) r
            * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro k hk θ
    have hkabs : (n : ℤ) ≤ |(k : ℤ)| := by
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ))]
      exact_mod_cast hk
    have hkabs' : (n : ℤ) ≤ |(-(k : ℤ))| := by
      rw [abs_neg]
      exact hkabs
    have hnat1 : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
    have hnat2 : ((-(k : ℤ))).natAbs = k := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    rw [hA (k : ℤ) hkabs r hr, hA (-(k : ℤ)) hkabs' r hr, hnat1, hnat2,
      hAneg k hk, h40 k hk r hr.1 θ]
    have hx1 : Complex.exp (((((k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)
            * Complex.exp (-((n : ℂ) * (θ : ℂ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hx2 : Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Complex.exp (-((k : ℂ) * (θ : ℂ)) * Complex.I)
            * Complex.exp (-((n : ℂ) * (θ : ℂ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hx1, hx2]
    ring
  -- the symmetric partial sum equals the partial sum of (19)
  have hsum : ∀ (N : ℕ) (θ : ℝ),
      (∑ j ∈ Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ),
          FourierCoefOfH n H j r
            * Complex.exp ((((j - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = ∑ k ∈ Finset.Icc n (n + N),
            Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro N θ
    induction N with
    | zero =>
        have hmid : ∀ j ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ),
            FourierCoefOfH n H j r
              * Complex.exp ((((j - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I) = 0 := by
          intro j hj
          simp only [Finset.mem_Ioo] at hj
          rw [hlow j (by omega), zero_mul]
        have hsplit : Finset.Icc (-((n + 0 : ℕ) : ℤ)) ((n + 0 : ℕ) : ℤ)
            = insert (-(n : ℤ)) (insert (n : ℤ) (Finset.Ioo (-(n : ℤ)) (n : ℤ))) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
          omega
        have hni : (n : ℤ) ∉ Finset.Ioo (-(n : ℤ)) (n : ℤ) := by simp
        have hnni : (-(n : ℤ)) ∉ insert (n : ℤ) (Finset.Ioo (-(n : ℤ)) (n : ℤ)) := by
          simp only [Finset.mem_insert, Finset.mem_Ioo]
          have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
          omega
        rw [hsplit, Finset.sum_insert hnni, Finset.sum_insert hni,
          Finset.sum_eq_zero hmid, add_zero,
          show Finset.Icc n (n + 0) = {n} from by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_singleton]
            omega,
          Finset.sum_singleton]
        have h := hpair n le_rfl θ
        push_cast at h ⊢
        linear_combination h
    | succ N ih =>
        have hsplit : Finset.Icc (-((n + (N + 1) : ℕ) : ℤ)) ((n + (N + 1) : ℕ) : ℤ)
            = insert (-((n + (N + 1) : ℕ) : ℤ))
                (insert (((n + (N + 1) : ℕ) : ℤ))
                  (Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ))) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          push_cast
          omega
        have hni : (((n + (N + 1) : ℕ) : ℤ))
            ∉ Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ) := by
          simp only [Finset.mem_Icc]
          push_cast
          omega
        have hnni : (-((n + (N + 1) : ℕ) : ℤ))
            ∉ insert (((n + (N + 1) : ℕ) : ℤ))
                (Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ)) := by
          simp only [Finset.mem_insert, Finset.mem_Icc]
          have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
          push_cast
          omega
        have hRsplit : Finset.Icc n (n + (N + 1))
            = insert (n + (N + 1)) (Finset.Icc n (n + N)) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hRni : (n + (N + 1)) ∉ Finset.Icc n (n + N) := by
          simp only [Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert hnni, Finset.sum_insert hni, ih,
          hRsplit, Finset.sum_insert hRni]
        have h := hpair (n + (N + 1)) (by omega) θ
        push_cast at h ⊢
        linear_combination h
  -- reindex part (f) by `M = n + N` and rewrite the summand
  have hcomp := (hfreg r hr').comp (Filter.tendsto_add_atTop_nat n)
  refine hcomp.congr (fun N => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  show ‖_ - ∑ j ∈ Finset.Icc (-((N + n : ℕ) : ℤ)) ((N + n : ℕ) : ℤ), _‖ ^ 2 = _
  rw [show (N + n : ℕ) = (n + N : ℕ) from by omega, hsum N θ]
