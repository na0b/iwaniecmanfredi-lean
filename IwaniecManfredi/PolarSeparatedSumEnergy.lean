import IwaniecManfredi.DiscEnergyPolarCoord
import IwaniecManfredi.TwoFamilyTrigParseval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option maxHeartbeats 1000000

open MeasureTheory

/-- The energy over the unit disc of a finite sum of polar-separated summands,
in closed form.

Suppose each `f_k`, `k ∈ F`, is polar-separated with radial exponent `e k` and
the two angular frequencies `g₁ k`, `g₂ k`:
`f_k(r e^{iθ}) = r^{e k} (γ_k e^{i g₁(k) θ} + δ_k e^{i g₂(k) θ})` for `r > 0`.
Suppose further that `e k > -1` on `F`, that `g₁` and `g₂` are each injective
on `F`, and that the two frequency families never collide.  Then
`∫_{‖ξ‖<1} ‖∑_{k ∈ F} f_k(ξ)‖² = ∑_{k ∈ F} 2π(‖γ_k‖² + ‖δ_k‖²)/(2 e k + 2)`.

This is the finite-sum engine for the display the paper calls "a standard
computation" at `paper.tex:351-353`,
`∫_0^1 r ∫_0^{2π} |H_r(r,θ)|² dθ dr = π Σ_{k>n} λ_k(1+ε_k²)|A_k|²`, which with
(24), (25) and (27) is what gives Theorem 2's bound (22).  Each summand of the
polar form (40) of the series (19) has exactly this shape, with the two
frequencies `k - n` and `-k - n`.

The three structural hypotheses are what make the answer a bare sum over `F`
rather than a double sum: all cross terms between distinct indices, and all
cross terms between the two frequency families, integrate to zero over a full
period.  The condition `e k > -1` is exactly the convergence condition for the
radial integral `∫_0^1 r^{2 e k + 1} dr = 1/(2 e k + 2)`, and it is where the
denominator comes from.  Both sides are `[0,∞]`-valued, so no integrability
hypothesis is needed; `-1 < e k` already forces the right-hand side finite. -/
theorem PolarSeparatedSumEnergy (fk : ℕ → ℂ → ℂ) (g1 g2 : ℕ → ℤ) (γ δ : ℕ → ℂ)
    (F : Finset ℕ) (e : ℕ → ℝ)
    (hmeasf : ∀ k, Measurable (fk k))
    (he : ∀ k ∈ F, -1 < e k)
    (hi1 : ∀ k ∈ F, ∀ k' ∈ F, g1 k = g1 k' → k = k')
    (hi2 : ∀ k ∈ F, ∀ k' ∈ F, g2 k = g2 k' → k = k')
    (hi12 : ∀ k ∈ F, ∀ k' ∈ F, g1 k ≠ g2 k')
    (hppol : ∀ k ∈ F, ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ((r ^ (e k) : ℝ) : ℂ)
          * (γ k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + δ k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) :
    (∫⁻ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ENNReal.ofReal (‖∑ k ∈ F, fk k ξ‖ ^ 2))
      = ∑ k ∈ F, ENNReal.ofReal
          (2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2) / (2 * e k + 2)) := by
  -- the finite-Parseval alias, in the application shape the angular step uses
  have hfinpars := fun (S : Finset ℕ) (a1 a2 : ℕ → ℤ) (c1 c2 : ℕ → ℂ) =>
    TwoFamilyTrigParseval S a1 a2 c1 c2
  have hSmeas : Measurable (fun ξ : ℂ => ∑ k ∈ F, fk k ξ) :=
    Finset.measurable_sum F (fun k _ => hmeasf k)
  rw [← DiscEnergyPolarCoord _ hSmeas]
  -- the angular value at each radius
  have hangval : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖∑ k ∈ F,
            fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
        = ENNReal.ofReal (2 * Real.pi * ∑ k ∈ F,
            (r ^ (e k)) ^ 2 * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)) := by
    intro r hr
    have hint : ∀ θ : ℝ, (∑ k ∈ F, fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        = ∑ k ∈ F, ((((r ^ (e k) : ℝ) : ℂ) * γ k)
              * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + (((r ^ (e k) : ℝ) : ℂ) * δ k)
              * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      intro θ
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hppol k hk r hr θ]
      ring
    have hScont : Continuous (fun θ : ℝ =>
        ∑ k ∈ F, fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      rw [show (fun θ : ℝ => ∑ k ∈ F, fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          = (fun θ : ℝ => ∑ k ∈ F,
            ((((r ^ (e k) : ℝ) : ℂ) * γ k)
                * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + (((r ^ (e k) : ℝ) : ℂ) * δ k)
                * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
        from funext hint]
      refine continuous_finsetSum F (fun k _ => ?_)
      fun_prop
    have hII : IntervalIntegrable (fun θ : ℝ =>
        ‖∑ k ∈ F, fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      ((hScont.norm).pow 2).intervalIntegrable _ _
    rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hII.1
        (Filter.Eventually.of_forall (fun θ => by positivity)),
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    congr 1
    rw [intervalIntegral.integral_congr (fun θ _ => by rw [hint θ])]
    rw [hfinpars F g1 g2 (fun k => ((r ^ (e k) : ℝ) : ℂ) * γ k)
      (fun k => ((r ^ (e k) : ℝ) : ℂ) * δ k) hi1 hi2 hi12]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hrp : (0 : ℝ) < r ^ (e k) := Real.rpow_pos_of_pos hr _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
    ring
  -- the radial integral
  have hcongr : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal r * (∫⁻ θ in Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (‖∑ k ∈ F,
            fk k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2))
        = ∑ k ∈ F, ENNReal.ofReal (2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
            * r ^ (2 * e k + 1)) := by
    intro r hr
    have hreal : r * (2 * Real.pi * ∑ k ∈ F,
          (r ^ (e k)) ^ 2 * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2))
        = ∑ k ∈ F, 2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
            * r ^ (2 * e k + 1) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hpw : r * (r ^ (e k)) ^ 2
          = r ^ (2 * e k + 1) := by
        rw [← Real.rpow_natCast (r ^ (e k)) 2, ← Real.rpow_mul hr.1.le,
          show (2 * e k + 1)
            = 1 + (e k) * ((2 : ℕ) : ℝ) from by push_cast; ring,
          Real.rpow_add hr.1, Real.rpow_one]
      calc r * (2 * Real.pi * ((r ^ (e k)) ^ 2 * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)))
          = 2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
              * (r * (r ^ (e k)) ^ 2) := by ring
        _ = 2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2) * r ^ (2 * e k + 1) := by
            rw [hpw]
    rw [hangval r hr.1, ← ENNReal.ofReal_mul hr.1.le, hreal,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => by
        have h1 : (0 : ℝ) ≤ r ^ (2 * e k + 1) := Real.rpow_nonneg hr.1.le _
        positivity)]
  have hmeask : ∀ k ∈ F, Measurable (fun r : ℝ =>
      ENNReal.ofReal (2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
        * r ^ (2 * e k + 1))) := by
    intro k _
    exact ENNReal.measurable_ofReal.comp
      ((measurable_id.pow measurable_const).const_mul _)
  have hterm : ∀ k ∈ F, (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
          * r ^ (2 * e k + 1)))
      = ENNReal.ofReal (2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2) / (2 * e k + 2)) := by
    intro k hk
    have hlk := he k hk
    have hc0 : (0 : ℝ) ≤ 2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2) := by positivity
    have hint1 : IntervalIntegrable
        (fun r : ℝ => r ^ (2 * e k + 1)) MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hval : (∫ r in (0 : ℝ)..1, r ^ (2 * e k + 1))
        = 1 / (2 * e k + 2) := by
      rw [integral_rpow (Or.inl (by linarith)),
        show 2 * e k + 1 + 1 = 2 * e k + 2 from by ring,
        Real.one_rpow, Real.zero_rpow (by linarith : (0:ℝ) < 2 * e k + 2).ne']
      ring
    have hnn : ∀ᵐ r : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)),
        (0 : ℝ) ≤ 2 * Real.pi * (‖γ k‖ ^ 2 + ‖δ k‖ ^ 2)
          * r ^ (2 * e k + 1) := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun r hr => ?_))
      have h1 : (0 : ℝ) ≤ r ^ (2 * e k + 1) := Real.rpow_nonneg hr.1.le _
      positivity
    rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hint1.const_mul _).1) hnn,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, hval]
    congr 1
    field_simp
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hcongr,
    MeasureTheory.lintegral_finsetSum _ (fun k hk => hmeask k hk)]
  exact Finset.sum_congr rfl hterm
