import IwaniecManfredi.Thm2TermGeometricSummability
import IwaniecManfredi.FourierCoefOfH
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option maxHeartbeats 1000000

open MeasureTheory

/-- The circlewise Fourier coefficient (30) of the series (19), evaluated by
term-by-term integration.

Two statements about the same computation.  Conjunct (a) is the per-summand
algebra: against the frequency `e^{i(n-j)θ}` of (30), the `(n+m)`-th summand of
(19) at the point `r e^{iθ}` is a sum of exactly two pure angular
exponentials, of frequencies `(n+m)-j` and `-(n+m)-j`, each carried by the
single radial factor `r^{λ_{n+m}}`:

`T_{n+m}(r e^{iθ}) e^{i(n-j)θ}`
`  = r^{λ_{n+m}} A_{n+m} e^{i((n+m)-j)θ}`
`    + r^{λ_{n+m}} ε_{n+m} conj(A_{n+m}) e^{i(-(n+m)-j)θ}`.

Conjunct (b) is its consequence for the coefficient: integrating over the
circle annihilates every frequency but zero, so the `j`-th coefficient of the
series picks out only the indices with `n+m = j` or `n+m = -j`, and

`a_j(r) = (1/2π) Σ_m 2π r^{λ_{n+m}} ( [n+m = j] A_{n+m}`
`                                     + [n+m = -j] ε_{n+m} conj(A_{n+m}) )`.

This is the paper's (29)/(40) read on the series rather than on an abstract
solution of (18): it is what identifies the coefficients of the constructed
`H` as `A_k r^{λ_k}` for `|k| ≥ n`, and zero otherwise, since for `|j| < n` no
index `n+m` meets either selection.  The `2π` left standing inside the sum is
the one that cancels against the `1/(2π)` of `FourierCoefOfH`; it is kept
unevaluated so that the identity is exactly what term-by-term integration
produces.

The function is the series completed at the origin by the value `A_n` of the
constant summand `T_n`, written out as the `if`-expression rather than named,
so that the statement depends on nothing but `n`, `p` and `A`.  The value at
the origin is irrelevant to both conjuncts, which only ever evaluate at
`r e^{iθ}` with `r > 0`.

Term-by-term integration is legitimate because `Σ_m ‖T_{n+m}‖` converges
uniformly on each circle `|ξ| = r < 1`, which is the geometric domination of
`Thm2TermGeometricSummability`. -/
theorem Thm2SeriesCircleFourierCoef (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (A : ℤ → ℂ)
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    (∀ (m : ℕ) (j : ℤ) (r : ℝ), 0 < r → ∀ θ : ℝ,
      Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * A ((n : ℤ) + (m : ℤ))
              * Complex.exp (((((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * (((EpsCoef n (n + m) p : ℝ) : ℂ)
                * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
              * Complex.exp (((-((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ)
                  * (θ : ℂ) * Complex.I))
    ∧ (∀ (j : ℤ) (r : ℝ), 0 < r → r < 1 →
      FourierCoefOfH n (fun ξ : ℂ => if ξ = 0 then A (n : ℤ)
          else ∑' m : ℕ, Thm2Term n p A (n + m) ξ) j r
        = (1 / (2 * Real.pi) : ℂ) * ∑' m : ℕ,
            (((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
              * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
                + (if ((n : ℤ) + (m : ℤ)) = -j then
                    ((EpsCoef n (n + m) p : ℝ) : ℂ)
                      * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0)))) := by
  -- the summability engine supplies the pointwise bound on each summand and the
  -- geometric domination that licenses term-by-term integration
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hT2, hgeo0⟩ :=
    Thm2TermGeometricSummability n p hn hp A hsum
  set H : ℂ → ℂ := fun ξ => if ξ = 0 then A (n : ℤ) else ∑' m : ℕ, Thm2Term n p A (n + m) ξ
    with hHdef
  have hHval : ∀ ξ : ℂ, ξ ≠ 0 → H ξ = ∑' m : ℕ, Thm2Term n p A (n + m) ξ := by
    intro ξ hξ
    simp only [hHdef]
    rw [if_neg hξ]
  have hcirc : ∀ (r : ℝ), 0 < r → ∀ θ : ℝ,
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := fun r hr θ =>
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) (Complex.exp_ne_zero _)
  have hcircnorm : ∀ (r : ℝ), 0 < r → ∀ θ : ℝ,
      ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
    intro r hr θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hnormexp : ∀ (c : ℤ) (θ : ℝ),
      ‖Complex.exp (((c : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    intro c θ
    rw [show (((c : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = (((((c : ℤ) : ℝ)) * θ : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have horth : ∀ l : ℤ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = if l = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    intro l
    have heq : ∀ θ : ℝ, Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Complex.exp ((((l : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
      intro θ; congr 1; ring
    rw [intervalIntegral.integral_congr
      (g := fun θ : ℝ => Complex.exp ((((l : ℤ) : ℂ) * Complex.I) * (θ : ℂ)))
      (fun θ _ => heq θ)]
    by_cases h : l = 0
    · rw [if_pos h, h]
      simp
    · rw [if_neg h]
      have hc : (((l : ℤ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (Int.cast_ne_zero.mpr h) Complex.I_ne_zero
      rw [integral_exp_mul_complex hc]
      have h1 : ((l : ℤ) : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)
          = (l : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h1, Complex.exp_int_mul_two_pi_mul_I]
      simp
  have hpolar : ∀ (m : ℕ) (j : ℤ) (r : ℝ), 0 < r → ∀ θ : ℝ,
      Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * A ((n : ℤ) + (m : ℤ))
              * Complex.exp (((((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * (((EpsCoef n (n + m) p : ℝ) : ℂ)
                * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
              * Complex.exp (((-((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ)
                  * (θ : ℂ) * Complex.I) := by
    intro m j r hr θ
    have hb := (Thm2TermSolvesEq18 n p hn hp (n + m) (by omega) A).2.1 r hr θ
    have hcastA : A (((n + m : ℕ)) : ℤ) = A ((n : ℤ) + (m : ℤ)) := by congr 1
    rw [hb, hcastA]
    rw [show (((((n : ℕ) + m : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ) = ((m : ℤ) : ℂ) from by
      push_cast; ring]
    rw [show ((-(((n : ℕ) + m : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ)
        = ((-((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ) from by push_cast; ring]
    rw [show (((((n : ℤ) + (m : ℤ)) - j : ℤ)) : ℂ)
        = ((m : ℤ) : ℂ) + (((n : ℤ) - j : ℤ) : ℂ) from by push_cast; ring]
    rw [show ((-((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ)
        = ((-((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ) + (((n : ℤ) - j : ℤ) : ℂ) from by
      push_cast; ring]
    rw [show (((m : ℤ) : ℂ) + (((n : ℤ) - j : ℤ) : ℂ)) * (θ : ℂ) * Complex.I
        = ((m : ℤ) : ℂ) * (θ : ℂ) * Complex.I
          + (((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I from by ring, Complex.exp_add]
    rw [show (((-((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ) + (((n : ℤ) - j : ℤ) : ℂ))
          * (θ : ℂ) * Complex.I
        = ((-((n : ℤ) + (m : ℤ)) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I
          + (((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I from by ring, Complex.exp_add]
    ring
  have hcontint : ∀ (m : ℕ) (j : ℤ) (r : ℝ), 0 < r → Continuous (fun θ : ℝ =>
      Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
    intro m j r hr
    rw [show (fun θ : ℝ =>
        Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
      = (fun θ : ℝ => ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * A ((n : ℤ) + (m : ℤ))
              * Complex.exp (((((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ) * (((EpsCoef n (n + m) p : ℝ) : ℂ)
                * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
              * Complex.exp (((-((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
      from funext (hpolar m j r hr)]
    fun_prop
  have hTint : ∀ (m : ℕ) (j : ℤ) (r : ℝ), 0 < r →
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = ((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
            * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
              + (if ((n : ℤ) + (m : ℤ)) = -j then
                  ((EpsCoef n (n + m) p : ℝ) : ℂ)
                    * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0)) := by
    intro m j r hr
    rw [intervalIntegral.integral_congr (fun θ _ => hpolar m j r hr θ)]
    have hc1 : Continuous (fun θ : ℝ => ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
        * A ((n : ℤ) + (m : ℤ))
        * Complex.exp (((((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      fun_prop
    have hc2 : Continuous (fun θ : ℝ => ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
        * (((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))))
        * Complex.exp (((-((n : ℤ) + (m : ℤ)) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      fun_prop
    rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, horth, horth]
    by_cases h1 : ((n : ℤ) + (m : ℤ)) = j
    · rw [if_pos h1, if_neg (by omega : ¬ (((n : ℤ) + (m : ℤ)) = -j)),
        if_pos (by omega : ((n : ℤ) + (m : ℤ)) - j = 0),
        if_neg (by omega : ¬ (-((n : ℤ) + (m : ℤ)) - j = 0))]
      ring
    · by_cases h2 : ((n : ℤ) + (m : ℤ)) = -j
      · rw [if_neg h1, if_pos h2, if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ)) - j = 0),
          if_pos (by omega : -((n : ℤ) + (m : ℤ)) - j = 0)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (by omega : ¬ ((n : ℤ) + (m : ℤ)) - j = 0),
          if_neg (by omega : ¬ (-((n : ℤ) + (m : ℤ)) - j = 0))]
        ring
  have hFour : ∀ (j : ℤ) (r : ℝ), 0 < r → r < 1 →
      FourierCoefOfH n H j r
        = (1 / (2 * Real.pi) : ℂ) * ∑' m : ℕ,
            (((2 * Real.pi : ℝ) : ℂ) * ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
              * ((if ((n : ℤ) + (m : ℤ)) = j then A ((n : ℤ) + (m : ℤ)) else 0)
                + (if ((n : ℤ) + (m : ℤ)) = -j then
                    ((EpsCoef n (n + m) p : ℝ) : ℂ)
                      * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ))) else 0))) := by
    intro j r hr hr1
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    simp only [FourierCoefOfH]
    congr 1
    rw [intervalIntegral.integral_of_le h2pi]
    have heq : ∀ θ : ℝ, H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = ∑' m : ℕ, (Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      intro θ
      rw [hHval _ (hcirc r hr θ), ← tsum_mul_right]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => heq θ)]
    have hmeasf : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
      fun m => (hcontint m j r hr).aestronglyMeasurable
    have hptw : ∀ (m : ℕ) (θ : ℝ),
        ‖Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ₑ
          ≤ ENNReal.ofReal (2 * ‖A ((n : ℤ) + (m : ℤ))‖
              * r ^ LambdaCoef n (n + m) p) := by
      intro m θ
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, hnormexp ((n : ℤ) - j) θ, mul_one]
      have h := hT2 m ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (hcirc r hr θ)
      rwa [hcircnorm r hr θ] at h
    have hfin : (∑' m : ℕ, ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
        ‖Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ₑ) ≠ ⊤ := by
      have hb1 : ∀ m : ℕ, (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
            ‖Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ₑ)
          ≤ ENNReal.ofReal (2 * ‖A ((n : ℤ) + (m : ℤ))‖ * r ^ LambdaCoef n (n + m) p)
              * ENNReal.ofReal (2 * Real.pi) := by
        intro m
        calc (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
              ‖Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                * Complex.exp ((((n : ℤ) - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ₑ)
            ≤ ∫⁻ _θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
                ENNReal.ofReal (2 * ‖A ((n : ℤ) + (m : ℤ))‖
                  * r ^ LambdaCoef n (n + m) p) :=
              MeasureTheory.lintegral_mono (fun θ => hptw m θ)
          _ = ENNReal.ofReal (2 * ‖A ((n : ℤ) + (m : ℤ))‖ * r ^ LambdaCoef n (n + m) p)
                * MeasureTheory.volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) :=
              MeasureTheory.setLIntegral_const _ _
          _ = ENNReal.ofReal (2 * ‖A ((n : ℤ) + (m : ℤ))‖ * r ^ LambdaCoef n (n + m) p)
                * ENNReal.ofReal (2 * Real.pi) := by
              rw [Real.volume_Ioc, sub_zero]
      refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb1) ?_)
      rw [ENNReal.tsum_mul_right,
        ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (hgeo0 r hr hr1)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    rw [MeasureTheory.integral_tsum hmeasf hfin]
    refine tsum_congr (fun m => ?_)
    rw [← intervalIntegral.integral_of_le h2pi, hTint m j r hr]
  exact ⟨hpolar, hFour⟩
