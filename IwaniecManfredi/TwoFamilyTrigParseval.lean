import IwaniecManfredi.Preamble
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option maxHeartbeats 1000000

/-- Parseval's identity for a finite trigonometric sum built from two
frequency families: if `g₁, g₂ : ℕ → ℤ` are each injective on a finite set `F`
and never take a common value there, then for coefficients `c₁, c₂`
`∫₀^{2π} ‖∑_{k ∈ F} (c₁ k e^{i g₁(k) θ} + c₂ k e^{i g₂(k) θ})‖² dθ
  = 2π ∑_{k ∈ F} (‖c₁ k‖² + ‖c₂ k‖²)`.

This is the Parseval step of the energy computation of Section 4
(`paper.tex:353-357`): each summand `T_k` of the series (19) has, on the circle
of radius `r`, exactly the two frequencies `k - n` and `-k - n`, the first
family injective in `k`, the second injective in `k`, and the two families
disjoint because `(k - n) - (-k' - n) = k + k' > 0`.  Applying this identity to
a partial sum and then integrating in `r` is what produces the
`π ∑ λ_k (1 + ε_k²) |A_k|²` of the energy identity.

The three hypotheses are exactly what makes the diagonal the whole story: the
two injectivity assumptions kill the off-diagonal pairs inside each family,
and the non-collision assumption kills every cross pair.  Nothing is assumed
about the sign or size of the frequencies, and `F` is an arbitrary finite set
of indices, so the identity applies to any partial sum. -/
theorem TwoFamilyTrigParseval (F : Finset ℕ) (g1 g2 : ℕ → ℤ) (c1 c2 : ℕ → ℂ)
    (h1 : ∀ k ∈ F, ∀ k' ∈ F, g1 k = g1 k' → k = k')
    (h2 : ∀ k ∈ F, ∀ k' ∈ F, g2 k = g2 k' → k = k')
    (h12 : ∀ k ∈ F, ∀ k' ∈ F, g1 k ≠ g2 k') :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖∑ k ∈ F, (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))‖ ^ 2)
      = 2 * Real.pi * ∑ k ∈ F, (‖c1 k‖ ^ 2 + ‖c2 k‖ ^ 2) := by
  -- orthogonality of the characters over a full period, the one ambient fact
  -- the block used from its old surroundings
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
  have hI : ∀ (l : ℤ) (c : ℂ), IntervalIntegrable
      (fun θ : ℝ => c * Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    intro l c
    have hc : Continuous
        (fun θ : ℝ => c * Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by fun_prop
    exact hc.intervalIntegrable _ _
  have hsum4 : ∀ (d1 d2 d3 d4 : ℂ) (l1 l2 l3 l4 : ℤ),
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (d1 * Complex.exp (((l1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + d2 * Complex.exp (((l2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + d3 * Complex.exp (((l3 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + d4 * Complex.exp (((l4 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
        = d1 * (if l1 = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0)
          + d2 * (if l2 = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0)
          + d3 * (if l3 = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0)
          + d4 * (if l4 = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
    intro d1 d2 d3 d4 l1 l2 l3 l4
    rw [intervalIntegral.integral_add (((hI l1 d1).add (hI l2 d2)).add (hI l3 d3)) (hI l4 d4),
      intervalIntegral.integral_add ((hI l1 d1).add (hI l2 d2)) (hI l3 d3),
      intervalIntegral.integral_add (hI l1 d1) (hI l2 d2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      horth, horth, horth, horth]
  have hEc : ∀ (l : ℤ) (θ : ℝ),
      starRingEnd ℂ (Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = Complex.exp (((-l : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro l θ
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  have hEE : ∀ (l l' : ℤ) (θ : ℝ),
      Complex.exp (((l : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          * Complex.exp (((-l' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Complex.exp (((l - l' : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro l l' θ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the per-pair integral
  have hpair : ∀ k : ℕ, k ∈ F → ∀ k' : ℕ, k' ∈ F →
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
            * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
        = if k = k' then ((2 * Real.pi : ℝ) : ℂ) * (((‖c1 k‖ ^ 2 + ‖c2 k‖ ^ 2 : ℝ)) : ℂ)
          else 0 := by
    intro k hk k' hk'
    have hrw : ∀ θ : ℝ,
        (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
            * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
          = (c1 k * starRingEnd ℂ (c1 k'))
              * Complex.exp (((g1 k - g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + (c1 k * starRingEnd ℂ (c2 k'))
              * Complex.exp (((g1 k - g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + (c2 k * starRingEnd ℂ (c1 k'))
              * Complex.exp (((g2 k - g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + (c2 k * starRingEnd ℂ (c2 k'))
              * Complex.exp (((g2 k - g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
      intro θ
      rw [map_add, map_mul, map_mul, hEc (g1 k'), hEc (g2 k')]
      rw [← hEE (g1 k) (g1 k'), ← hEE (g1 k) (g2 k'), ← hEE (g2 k) (g1 k'),
        ← hEE (g2 k) (g2 k')]
      ring
    rw [intervalIntegral.integral_congr (fun θ _ => hrw θ), hsum4]
    have hc12 : ¬(g1 k - g2 k' = 0) := fun h => h12 k hk k' hk' (by omega)
    have hc21 : ¬(g2 k - g1 k' = 0) := fun h => h12 k' hk' k hk (by omega)
    rw [if_neg hc12, if_neg hc21]
    by_cases hkk : k = k'
    · subst hkk
      rw [if_pos (show g1 k - g1 k = 0 by omega), if_pos (show g2 k - g2 k = 0 by omega),
        if_pos (show k = k from rfl), Complex.mul_conj, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · rw [if_neg hkk,
        if_neg (show ¬(g1 k - g1 k' = 0) from fun h => hkk (h1 k hk k' hk' (by omega))),
        if_neg (show ¬(g2 k - g2 k' = 0) from fun h => hkk (h2 k hk k' hk' (by omega)))]
      ring
  -- assemble
  have hcontterm : ∀ k : ℕ, Continuous (fun θ : ℝ =>
      c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
    intro k
    fun_prop
  have hC : ∀ θ : ℝ,
      ((‖∑ k ∈ F, (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))‖ ^ 2 : ℝ) : ℂ)
        = ∑ k ∈ F, ∑ k' ∈ F,
            (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
              * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
                + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  have hint0 : ∀ k k' : ℕ, IntervalIntegrable
      (fun θ : ℝ =>
        (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
          * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    intro k k'
    exact ((hcontterm k).mul (Complex.continuous_conj.comp (hcontterm k'))).intervalIntegrable _ _
  have hint1 : ∀ k : ℕ, IntervalIntegrable
      (fun θ : ℝ => ∑ k' ∈ F,
        (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
          * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    intro k
    have hfe : (fun θ : ℝ => ∑ k' ∈ F,
          (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
            * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
        = ∑ k' ∈ F, (fun θ : ℝ =>
          (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
            * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) := by
      funext θ
      rw [Finset.sum_apply]
    rw [hfe]
    exact IntervalIntegrable.sum F (fun k' _ => hint0 k k')
  have hgoalC : ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖∑ k ∈ F, (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))‖ ^ 2 : ℝ) : ℂ)
      = ((2 * Real.pi * ∑ k ∈ F, (‖c1 k‖ ^ 2 + ‖c2 k‖ ^ 2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal,
      intervalIntegral.integral_congr (fun θ _ => hC θ),
      intervalIntegral.integral_finsetSum (fun k _ => hint1 k)]
    have hinner : ∀ k ∈ F, (∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ k' ∈ F,
          (c1 k * Complex.exp (((g1 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
            + c2 k * Complex.exp (((g2 k : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
            * starRingEnd ℂ (c1 k' * Complex.exp (((g1 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + c2 k' * Complex.exp (((g2 k' : ℤ) : ℂ) * (θ : ℂ) * Complex.I)))
        = ((2 * Real.pi : ℝ) : ℂ) * (((‖c1 k‖ ^ 2 + ‖c2 k‖ ^ 2 : ℝ)) : ℂ) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun k' _ => hint0 k k'),
        Finset.sum_congr rfl (fun k' hk' => hpair k hk k' hk'),
        Finset.sum_ite_eq F k (fun _ => ((2 * Real.pi : ℝ) : ℂ)
          * (((‖c1 k‖ ^ 2 + ‖c2 k‖ ^ 2 : ℝ)) : ℂ)), if_pos hk]
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    push_cast
    ring
  exact Complex.ofReal_injective hgoalC
