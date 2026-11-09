import IwaniecManfredi.CoefCompatAndSeries
import IwaniecManfredi.EnergyIdentity
import IwaniecManfredi.Eq18ImpliesQuasiregular
import IwaniecManfredi.Thm2SeriesW12Convergence

open MeasureTheory

/-- The forward half of Theorem 2: every `W^{1,2}(B)` solution of (18) on the
unit disk expands into the series (19), with coefficients obeying (39) and the
bound (22), the series converging in `W^{1,2}(B)`.  The hypotheses are exactly
Theorem 2's: a `W^{1,2}(B)` solution of (18), together with the normalisations
`H ∈ C(B) ∩ C^∞(B - {0})` that paper.tex:183 licenses.  There is no `K` and no
`p ≠ 2`: quasiregularity is obtained internally with
`K = max (p-1) (1/(p-1))`, which turns the constant `C(n,p,K)` of the energy
identity into (22)'s `C(n,p)`. -/
theorem Thm2Expansion (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℂ → ℂ,
        MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H →
        ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1} →
        (∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ) →
        SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H →
        IntegrableOn (fun ξ : ℂ => ‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)
          {ξ : ℂ | ‖ξ‖ < 1} volume →
        ∃ A : ℤ → ℂ,
          (∀ k : ℤ, (n : ℤ) ≤ k →
            A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k)) ∧
          (∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
            FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)) ∧
          Summable (fun m : ℕ =>
              ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) ∧
          (∑' m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2
            ≤ C * ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2)) ∧
          Filter.Tendsto
            (fun N : ℕ =>
              (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
                  ‖H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k ξ‖ ^ 2)
              + (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
                  ‖DZ H ξ
                    - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2)
              + (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
                  ‖DZbar H ξ
                    - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) ξ‖ ^ 2))
            Filter.atTop (nhds 0) := by
  -- ## Step 0/1: the constant.  `Eq18ImpliesQuasiregular` produces exactly the paper's
  -- `K = max {p-1, 1/(p-1)}`, so `EnergyIdentity` is instantiated at that `K` and its
  -- constant, depending on `n`, `p` and `K` only, is (22)'s `C(n,p)`.
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK : (1 : ℝ) ≤ max (p - 1) (1 / (p - 1)) := by
    rcases le_or_gt 2 p with h2 | h2
    · exact le_trans (by linarith) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hp1]
      linarith
  obtain ⟨C, hC0, hEI⟩ := EnergyIdentity n p (max (p - 1) (1 / (p - 1))) hn hp hK
  refine ⟨C, hC0, ?_⟩
  intro H hW hc hdiff h18 hint
  -- ## Step 2: the coefficient family, chosen out of the second case of (36)
  obtain ⟨hacont, -, -, -, -, -⟩ := FourierCoefRegularity n H hc hW hdiff
  obtain ⟨hode1, hode2, hsm⟩ := FourierCoefOde n p hn hp H hc hW hdiff h18
  have hF36 : ∀ j : ℤ,
      (j.natAbs < n → ∀ r ∈ Set.Ico (0 : ℝ) 1, FourierCoefOfH n H j r = 0)
      ∧ (n ≤ j.natAbs → ∃ a : ℂ, ∀ r ∈ Set.Ico (0 : ℝ) 1,
          FourierCoefOfH n H j r = a * ((r ^ LambdaCoef n j.natAbs p : ℝ) : ℂ)) := fun j =>
    FourierCoefForm36 n p j hn hp (FourierCoefOfH n H j) (hacont j) (hsm j)
      (fun s hs => hode2 j s hs)
  have habs : ∀ j : ℤ, (n : ℤ) ≤ |j| ↔ n ≤ j.natAbs := by
    intro j
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le
  obtain ⟨A, hAval⟩ : ∃ A : ℤ → ℂ, ∀ j : ℤ, (n : ℤ) ≤ |j| → ∀ r ∈ Set.Ico (0 : ℝ) 1,
      FourierCoefOfH n H j r = A j * ((r ^ LambdaCoef n j.natAbs p : ℝ) : ℂ) := by
    refine ⟨fun j => if h : n ≤ j.natAbs then ((hF36 j).2 h).choose else 0, ?_⟩
    intro j hj r hr
    have h : n ≤ j.natAbs := (habs j).mp hj
    simp only [dif_pos h]
    exact ((hF36 j).2 h).choose_spec r hr
  have hAioo : ∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ) :=
    fun k hk r hr => hAval k hk r ⟨le_of_lt hr.1, hr.2⟩
  -- ## Step 3: the compatibility relation (39), with the corner `k = n` included
  obtain ⟨-, hAn, h39, -, -⟩ := CoefCompatAndSeries n p hn hp H hc hW hdiff h18 A hAioo
  obtain ⟨hlamn, hepsn, -, -⟩ := LambdaEpsEstimates n p hn hp
  have hcomp : ∀ k : ℤ, (n : ℤ) ≤ k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k) := by
    intro k hk
    rcases eq_or_lt_of_le hk with heq | hlt
    · rw [← heq, Int.natAbs_natCast, hAn, hepsn]
      simp
    · exact h39 k hlt
  -- ## Step 4: quasiregularity, then the energy identity at this `K`
  have hqr := Eq18ImpliesQuasiregular p hp n {ξ : ℂ | ‖ξ‖ < 1} H hW h18
  obtain ⟨-, -, hsum1, hbound, -⟩ := hEI H A hc hdiff h18 hqr hint hAioo
    (fun k hk => h39 k hk)
  -- ## Step 5: the summability hypothesis (S), which starts at `n` rather than `n+1`
  have hsumn : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) := by
    refine (summable_nat_add_iff 1).mp ?_
    rw [show (fun m : ℕ =>
          ((n : ℝ) + ((m + 1 : ℕ) : ℝ)) * ‖A ((n : ℤ) + ((m + 1 : ℕ) : ℤ))‖ ^ 2)
        = (fun m : ℕ => ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2) from by
      funext m
      push_cast
      ring_nf]
    exact hsum1
  -- ## Step 6: the sum of the series (19) for this `A`
  obtain ⟨H', hH'cont, hH'cd, hH'W, hH'int, hH'four, hH'four0, hH'tend⟩ :=
    Thm2SeriesW12Convergence n p hn hp A hcomp hsumn
  -- ## Step 7: `H = H'` on the disc, by uniqueness of Fourier coefficients
  have hEqOn : Set.EqOn H H' {ξ : ℂ | ‖ξ‖ < 1} := by
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hpi := Real.pi_pos
    -- off the origin: all Fourier coefficients of the difference vanish on each circle
    have hne : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 → H ξ = H' ξ := by
      intro ξ hξ0 hξ1
      have hr0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
      have hrIoo : ‖ξ‖ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hξ1⟩
      have hcirc : Continuous
          (fun θ : ℝ => ((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
        fun_prop
      have hcircmem : ∀ θ : ℝ,
          ((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
        intro θ
        show ‖_‖ < 1
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr0]
        exact hξ1
      have hHc : Continuous
          (fun θ : ℝ => H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
        hc.comp_continuous hcirc hcircmem
      have hH'c : Continuous
          (fun θ : ℝ => H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
        hH'cont.comp_continuous hcirc hcircmem
      have hgc : Continuous (fun θ : ℝ =>
          H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := hHc.sub hH'c
      -- the two families of coefficients agree, index by index
      have hcoefeq : ∀ m : ℤ,
          FourierCoefOfH n H ((n : ℤ) + m) ‖ξ‖ = FourierCoefOfH n H' ((n : ℤ) + m) ‖ξ‖ := by
        intro m
        rcases le_or_gt (n : ℤ) |((n : ℤ) + m)| with hge | hlt
        · rw [hAioo ((n : ℤ) + m) hge ‖ξ‖ hrIoo, hH'four ((n : ℤ) + m) hge ‖ξ‖ hrIoo]
        · have hj : ((n : ℤ) + m).natAbs < n := by
            rw [Int.abs_eq_natAbs] at hlt
            exact_mod_cast hlt
          rw [(hF36 ((n : ℤ) + m)).1 hj ‖ξ‖ ⟨le_of_lt hrIoo.1, hrIoo.2⟩,
            hH'four0 ((n : ℤ) + m) hlt ‖ξ‖ hrIoo]
      -- hence every Parseval coefficient of the difference is `0`
      have hgcoef : ∀ m : ℤ, (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I) = 0 := by
        intro m
        have hE : Continuous
            (fun θ : ℝ => Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)) := by fun_prop
        have hI1 : IntervalIntegrable
            (fun θ : ℝ => H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)) volume 0 (2 * Real.pi) :=
          (hHc.mul hE).intervalIntegrable _ _
        have hI2 : IntervalIntegrable
            (fun θ : ℝ => H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)) volume 0 (2 * Real.pi) :=
          (hH'c.mul hE).intervalIntegrable _ _
        have hexp : ∀ θ : ℝ, ((((n : ℤ) - ((n : ℤ) + m) : ℤ)) : ℂ) * (θ : ℂ) * Complex.I
            = -(m : ℂ) * (θ : ℂ) * Complex.I := by
          intro θ
          push_cast
          ring
        have hFH : FourierCoefOfH n H ((n : ℤ) + m) ‖ξ‖
            = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
                H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I) := by
          rw [FourierCoefOfH]
          congr 1
          exact intervalIntegral.integral_congr (fun θ _ => by rw [hexp θ])
        have hFH' : FourierCoefOfH n H' ((n : ℤ) + m) ‖ξ‖
            = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
                H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I) := by
          rw [FourierCoefOfH]
          congr 1
          exact intervalIntegral.integral_congr (fun θ _ => by rw [hexp θ])
        have hsub : (∫ θ in (0 : ℝ)..(2 * Real.pi),
              (H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I))
            = (∫ θ in (0 : ℝ)..(2 * Real.pi),
                H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I))
              - ∫ θ in (0 : ℝ)..(2 * Real.pi),
                H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I) := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          exact intervalIntegral.integral_congr (fun θ _ => by ring)
        rw [hsub, mul_sub, ← hFH, ← hFH', hcoefeq m, sub_self]
      -- Parseval then forces the `L²` norm of the difference to vanish
      have hpar := ParsevalOnCircle
        (fun θ : ℝ => H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        hgc.measurable ((hgc.norm.pow 2).integrableOn_Ioc)
      have hzero : (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) = 0 := by
        have he : (fun m : ℤ => 2 * Real.pi *
            ‖(1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              (H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
                  * Complex.exp (-(m : ℂ) * (θ : ℂ) * Complex.I)‖ ^ 2)
            = fun _ : ℤ => (0 : ℝ) := by
          funext m
          rw [hgcoef m]
          simp
        rw [he] at hpar
        exact (hasSum_zero.unique hpar).symm
      have hae : (fun θ : ℝ =>
          ‖H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
        refine (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae ?_
          ((hgc.norm.pow 2).integrableOn_Ioc)).mp ?_
        · filter_upwards with θ
          exact pow_two_nonneg _
        · rw [← intervalIntegral.integral_of_le h2pi]
          exact hzero
      have heqIoc := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
        ((hgc.norm.pow 2).continuousOn) continuousOn_const
      -- the argument of `ξ` lies in `(-π, π]`; normalise it into `(0, 2π]`
      have harg := Complex.arg_mem_Ioc ξ
      have hper : ∀ θ : ℝ, Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((θ : ℂ) * Complex.I) := by
        intro θ
        push_cast
        rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      have hfinish : ∀ θ : ℝ, θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) →
          ξ = ((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) → H ξ = H' ξ := by
        intro θ hθ hξθ
        have h0 := heqIoc hθ
        simp only [Pi.zero_apply] at h0
        rw [hξθ]
        have h1 : H (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - H' (((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
          simpa using h0
        linear_combination h1
      rcases le_or_gt (Complex.arg ξ) 0 with hnpos | hpos
      · refine hfinish (Complex.arg ξ + 2 * Real.pi) ⟨by linarith [harg.1], by linarith⟩ ?_
        rw [hper (Complex.arg ξ)]
        exact (Complex.norm_mul_exp_arg_mul_I ξ).symm
      · refine hfinish (Complex.arg ξ) ⟨hpos, by linarith [harg.2]⟩ ?_
        exact (Complex.norm_mul_exp_arg_mul_I ξ).symm
    -- at the origin, by continuity: `B` is contained in the closure of `B - {0}`
    refine Set.EqOn.of_subset_closure (s := {ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)})
      (fun z hz => hne z (by simpa using hz.2) hz.1) hc hH'cont Set.sdiff_subset ?_
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · refine Metric.mem_closure_iff.mpr (fun ε hε => ?_)
      have hmin : (0 : ℝ) < min ε 1 / 2 := by
        have : (0 : ℝ) < min ε 1 := lt_min hε one_pos
        linarith
      refine ⟨((min ε 1 / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
      · show ‖((min ε 1 / 2 : ℝ) : ℂ)‖ < 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmin]
        have := min_le_right ε 1
        linarith
      · simp only [Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact ne_of_gt hmin
      · rw [dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hmin]
        have := min_le_left ε 1
        linarith
    · exact subset_closure ⟨hz, by simpa using hz0⟩
  -- ## Step 8: transfer clause (g) of the series node to `H`
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hBmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} := hBopen.measurableSet
  have hDZeq : ∀ ξ ∈ {ξ : ℂ | ‖ξ‖ < 1}, DZ H ξ = DZ H' ξ ∧ DZbar H ξ = DZbar H' ξ := by
    intro ξ hξ
    have hfd : fderiv ℝ H ξ = fderiv ℝ H' ξ :=
      Filter.EventuallyEq.fderiv_eq
        (Filter.eventuallyEq_of_mem (hBopen.mem_nhds hξ) (fun z hz => hEqOn hz))
    exact ⟨by simp only [DZ, hfd], by simp only [DZbar, hfd]⟩
  refine ⟨A, hcomp, hAioo, hsum1, hbound, ?_⟩
  refine hH'tend.congr (fun N => ?_)
  congr 1
  · congr 1
    · exact MeasureTheory.setIntegral_congr_fun hBmeas
        (fun ξ hξ => by rw [hEqOn hξ])
    · exact MeasureTheory.setIntegral_congr_fun hBmeas
        (fun ξ hξ => by rw [(hDZeq ξ hξ).1])
  · exact MeasureTheory.setIntegral_congr_fun hBmeas
      (fun ξ hξ => by rw [(hDZeq ξ hξ).2])
