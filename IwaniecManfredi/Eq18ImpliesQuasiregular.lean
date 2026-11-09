import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.QuasiregularOn

/-- The paper's assertion at line 239 that a solution of (18) is
`K`-quasiregular with `K = max{p-1, 1/(p-1)}`.  Both bracketed factors of (18)
have modulus `1` off the origin, so `|H_ξ̄| ≤ 2|1/2 - 1/p| |H_ξ| =
(|p-2|/p)|H_ξ|`, and `(K-1)/(K+1) = |p-2|/p` exactly for that `K`.  This is
what lets Theorem 2's constant be `C(n,p)` rather than `C(n,p,K)`: no
quasiregularity needs to be hypothesised, it is a consequence of (18). -/
theorem Eq18ImpliesQuasiregular (p : ℝ) (hp : 1 < p) (n : ℕ) (Ω : Set ℂ) (H : ℂ → ℂ)
    (hW : MemWLocOn 1 2 Ω H) (h18 : SolvesEq18 n p Ω H) :
    QuasiregularOn (max (p - 1) (1 / (p - 1))) Ω H := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hp1ne : p - 1 ≠ 0 := ne_of_gt hp1
  have hp0ne : p ≠ 0 := ne_of_gt hp0
  -- `1 ≤ K` for `K = max (p-1) (1/(p-1))`.
  have hK1 : (1 : ℝ) ≤ max (p - 1) (1 / (p - 1)) := by
    by_cases h2 : (2 : ℝ) ≤ p
    · exact le_max_of_le_left (by linarith)
    · replace h2 : p < 2 := not_le.mp h2
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ hp1]
      nlinarith
  -- `(K-1)/(K+1) = |p-2|/p`.  After this the `max` is never unfolded again.
  have hratio : (max (p - 1) (1 / (p - 1)) - 1) / (max (p - 1) (1 / (p - 1)) + 1)
      = |p - 2| / p := by
    by_cases h2 : (2 : ℝ) ≤ p
    · have hmax : max (p - 1) (1 / (p - 1)) = p - 1 := by
        refine max_eq_left ?_
        rw [div_le_iff₀ hp1]
        nlinarith
      rw [hmax, abs_of_nonneg (show (0 : ℝ) ≤ p - 2 by linarith)]
      rw [show p - 1 + 1 = p from by ring]
      ring
    · replace h2 : p < 2 := not_le.mp h2
      have hmax : max (p - 1) (1 / (p - 1)) = 1 / (p - 1) := by
        refine max_eq_right ?_
        rw [le_div_iff₀ hp1]
        nlinarith
      have hden : (0 : ℝ) < 1 / (p - 1) + 1 := by
        have := one_div_pos.mpr hp1
        linarith
      rw [hmax, abs_of_neg (show p - 2 < 0 by linarith)]
      field_simp
      ring
  -- `|1/2 - 1/p| = |p-2|/(2p)`.
  have habs : |1 / 2 - 1 / p| = |p - 2| / (2 * p) := by
    rw [show (1 : ℝ) / 2 - 1 / p = (p - 2) / (2 * p) from by field_simp, abs_div,
      abs_of_pos (show (0 : ℝ) < 2 * p by positivity)]
  -- Almost every point of `ℂ` is nonzero, so (18)'s `ξ ≠ 0` hypothesis is free.
  have hne : ∀ᵐ ξ : ℂ, ξ ≠ 0 := by
    have h0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) {(0 : ℂ)} = 0 :=
      MeasureTheory.measure_singleton 0
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr h0] with x hx
    simpa using hx
  -- The witnessing pair of weak Wirtinger derivatives is the one (18) already supplies.
  obtain ⟨a, b, hab, hae⟩ := h18
  refine ⟨hK1, hW, a, b, hab, ?_⟩
  filter_upwards [hae, hne] with z hz hz0
  intro hzΩ
  rw [hz hzΩ hz0]
  have hzn : ‖z‖ ≠ 0 := by simpa using hz0
  have h1 : ‖(z / starRingEnd ℂ z) * a z‖ = ‖a z‖ := by
    rw [norm_mul, norm_div, RCLike.norm_conj, div_self hzn, one_mul]
  have h2 : ‖((starRingEnd ℂ z) ^ n / z ^ n) * starRingEnd ℂ (a z)‖ = ‖a z‖ := by
    rw [norm_mul, norm_div, norm_pow, norm_pow, RCLike.norm_conj, RCLike.norm_conj,
      div_self (pow_ne_zero n hzn), one_mul]
  calc ‖((1 / 2 - 1 / p : ℝ) : ℂ)
          * ((z / starRingEnd ℂ z) * a z
            + ((starRingEnd ℂ z) ^ n / z ^ n) * starRingEnd ℂ (a z))‖
      = ‖((1 / 2 - 1 / p : ℝ) : ℂ)‖
          * ‖(z / starRingEnd ℂ z) * a z
            + ((starRingEnd ℂ z) ^ n / z ^ n) * starRingEnd ℂ (a z)‖ := norm_mul _ _
    _ ≤ ‖((1 / 2 - 1 / p : ℝ) : ℂ)‖
          * (‖(z / starRingEnd ℂ z) * a z‖
            + ‖((starRingEnd ℂ z) ^ n / z ^ n) * starRingEnd ℂ (a z)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = |p - 2| / (2 * p) * (2 * ‖a z‖) := by
        rw [h1, h2, Complex.norm_real, Real.norm_eq_abs, habs]; ring
    _ = (max (p - 1) (1 / (p - 1)) - 1) / (max (p - 1) (1 / (p - 1)) + 1) * ‖a z‖ := by
        rw [hratio]; field_simp
