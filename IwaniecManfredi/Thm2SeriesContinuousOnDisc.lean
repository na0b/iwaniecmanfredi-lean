import IwaniecManfredi.Thm2TermGeometricSummability
import IwaniecManfredi.LambdaEpsEstimates
import IwaniecManfredi.Thm2TermSolvesEq18
set_option maxHeartbeats 1000000

/-- Conjunct (a) of Theorem 2 for the constructed solution: the sum of the
series (19) is continuous on the whole disc `𝔹`, the origin included.

The function is the series completed at the origin by the value `A_n` of its
constant summand `T_n`, written out as the `if`-expression rather than named,
so that the statement depends on nothing but `n`, `p` and `A`.

Off the origin this is local uniform convergence of a series of continuous
summands: on each closed annulus `‖x‖/2 < ‖z‖ < (‖x‖+1)/2` the summands are
dominated by the convergent numerical series `2|A_{n+m}| ρ^{λ_{n+m}}` taken at
the outer radius `ρ = (‖x‖+1)/2 < 1`.

At the origin it is the real content, and it is where the completing value is
forced.  Deleting the `m = 0` term, which is the constant `A_n`, leaves a tail
dominated by `8·CA·‖ξ‖^b`, where `b > 0` is the linear rate
`b·m ≤ λ_{n+m}` of `Thm2TermGeometricSummability` and `CA` its uniform bound
on the coefficients: each later summand carries `‖ξ‖^{λ_{n+m}} ≤ (‖ξ‖^b)^m`,
and once `‖ξ‖^b ≤ 1/2` that geometric factor sums.  Since `‖ξ‖^b → 0` as
`ξ → 0`, the sum tends to `A_n`, which is exactly the value the
`if`-expression assigns at the origin; so no other completion would be
continuous there. -/
theorem Thm2SeriesContinuousOnDisc (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (A : ℤ → ℂ)
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    ContinuousOn (fun ξ : ℂ => if ξ = 0 then A (n : ℤ)
        else ∑' m : ℕ, Thm2Term n p A (n + m) ξ) {ξ : ℂ | ‖ξ‖ < 1} := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the summability engine: the linear rate `b`, the coefficient bound `CA`, the
  -- geometric domination, and the pointwise bound on each summand
  obtain ⟨b, CA, hb0, _, _, _, hCA, hqbd, _, hTn, hT2, hgeo0⟩ :=
    Thm2TermGeometricSummability n p hn hp A hsum
  obtain ⟨hlamn, _, _, hlambd⟩ := LambdaEpsEstimates n p hn hp
  have hL0 : ∀ m : ℕ, 0 ≤ LambdaCoef n (n + m) p := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
    · have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
  have hTca : ∀ (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (Thm2Term n p A (n + m)) ξ :=
    fun m => (Thm2TermSolvesEq18 n p hn hp (n + m) (by omega) A).1
  set H : ℂ → ℂ := fun ξ => if ξ = 0 then A (n : ℤ) else ∑' m : ℕ, Thm2Term n p A (n + m) ξ
    with hHdef
  have hHval : ∀ ξ : ℂ, ξ ≠ 0 → H ξ = ∑' m : ℕ, Thm2Term n p A (n + m) ξ := by
    intro ξ hξ
    simp only [hHdef]
    rw [if_neg hξ]
  have hH0 : H 0 = A (n : ℤ) := by
    simp [hHdef]
  have hnormsum : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      Summable (fun m : ℕ => ‖Thm2Term n p A (n + m) ξ‖) := by
    intro ξ hξ hξ1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hT2 m ξ hξ)
      (hgeo0 ‖ξ‖ hr hξ1)
  have hHcontne : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 → ContinuousAt H x := by
    intro x hx hx1
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hd0 : (0 : ℝ) < ‖x‖ / 2 := by positivity
    have hde : ‖x‖ / 2 < ‖x‖ := by linarith
    have he0 : (0 : ℝ) < (‖x‖ + 1) / 2 := by linarith
    have hxe : ‖x‖ < (‖x‖ + 1) / 2 := by linarith
    have he1 : (‖x‖ + 1) / 2 < 1 := by linarith
    have hUopen : IsOpen {z : ℂ | ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + 1) / 2} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hxU : x ∈ {z : ℂ | ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + 1) / 2} := ⟨hde, hxe⟩
    have hUne : ∀ z ∈ {z : ℂ | ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + 1) / 2}, z ≠ 0 := by
      intro z hz hz0
      have h1 : ‖x‖ / 2 < ‖z‖ := hz.1
      rw [hz0, norm_zero] at h1
      linarith
    have hUcont : ContinuousOn (fun ξ : ℂ => ∑' m : ℕ, Thm2Term n p A (n + m) ξ)
        {z : ℂ | ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + 1) / 2} := by
      refine continuousOn_tsum (fun m z hz => ?_) (hgeo0 ((‖x‖ + 1) / 2) he0 he1)
        (fun m z hz => ?_)
      · exact ((hTca m z (hUne z hz)).continuousAt).continuousWithinAt
      · refine le_trans (hT2 m z (hUne z hz)) ?_
        have hle : ‖z‖ ^ LambdaCoef n (n + m) p
            ≤ ((‖x‖ + 1) / 2) ^ LambdaCoef n (n + m) p :=
          Real.rpow_le_rpow (norm_nonneg _) (le_of_lt hz.2) (hL0 m)
        have hA0 : (0 : ℝ) ≤ 2 * ‖A ((n : ℤ) + (m : ℤ))‖ := by positivity
        exact mul_le_mul_of_nonneg_left hle hA0
    have hEq : Set.EqOn H (fun ξ : ℂ => ∑' m : ℕ, Thm2Term n p A (n + m) ξ)
        {z : ℂ | ‖x‖ / 2 < ‖z‖ ∧ ‖z‖ < (‖x‖ + 1) / 2} :=
      fun z hz => hHval z (hUne z hz)
    exact (hUcont.congr hEq).continuousAt (hUopen.mem_nhds hxU)
  -- ## Step 4: continuity at the origin
  have htail : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 → ‖ξ‖ ^ b ≤ 1 / 2 →
      ‖H ξ - A (n : ℤ)‖ ≤ 8 * CA * ‖ξ‖ ^ b := by
    intro ξ hξ hξ1 hq2
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hq0 : 0 < ‖ξ‖ ^ b := Real.rpow_pos_of_pos hr b
    have hns := hnormsum ξ hξ hξ1
    have hs : Summable (fun m : ℕ => Thm2Term n p A (n + m) ξ) := Summable.of_norm hns
    have hsplit := hs.tsum_eq_add_tsum_ite 0
    have hzero : Thm2Term n p A (n + 0) ξ = A (n : ℤ) := by
      rw [Nat.add_zero]
      exact hTn ξ hξ
    have hHe : H ξ - A (n : ℤ) = ∑' m : ℕ, if m = 0 then 0 else Thm2Term n p A (n + m) ξ := by
      rw [hHval ξ hξ, hsplit, hzero]
      ring
    have hb1 : ∀ m : ℕ, ‖(if m = 0 then 0 else Thm2Term n p A (n + m) ξ)‖
        ≤ 4 * CA * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m := by
      intro m
      by_cases hm : m = 0
      · rw [if_pos hm, norm_zero]
        positivity
      · rw [if_neg hm]
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have h1 := hT2 m ξ hξ
        have h2 : ‖ξ‖ ^ LambdaCoef n (n + m) p ≤ (‖ξ‖ ^ b) ^ m := hqbd ‖ξ‖ hr hξ1 m
        have h3 : (2 * ‖ξ‖ ^ b) ^ m ≤ 2 * ‖ξ‖ ^ b := by
          calc (2 * ‖ξ‖ ^ b) ^ m ≤ (2 * ‖ξ‖ ^ b) ^ 1 :=
                pow_le_pow_of_le_one (by positivity) (by linarith) hm1
            _ = 2 * ‖ξ‖ ^ b := pow_one _
        have h4 : (‖ξ‖ ^ b) ^ m ≤ 2 * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m := by
          have hp2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
          rw [mul_pow] at h3
          rw [show (2 : ℝ) * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m
              = (2 * ‖ξ‖ ^ b) / 2 ^ m from by
            rw [div_pow, one_pow] at *
            ring]
          rw [le_div_iff₀ hp2]
          calc (‖ξ‖ ^ b) ^ m * 2 ^ m = 2 ^ m * (‖ξ‖ ^ b) ^ m := by ring
            _ ≤ 2 * ‖ξ‖ ^ b := h3
        have hA := hCA m
        have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
        calc ‖Thm2Term n p A (n + m) ξ‖
            ≤ 2 * ‖A ((n : ℤ) + (m : ℤ))‖ * ‖ξ‖ ^ LambdaCoef n (n + m) p := h1
          _ ≤ 2 * CA * (2 * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m) := by
              gcongr
              exact le_trans h2 h4
          _ = 4 * CA * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m := by ring
    have hmajs : Summable (fun m : ℕ => 4 * CA * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hns2 : Summable (fun m : ℕ =>
        ‖(if m = 0 then 0 else Thm2Term n p A (n + m) ξ)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb1 hmajs
    calc ‖H ξ - A (n : ℤ)‖
        = ‖∑' m : ℕ, if m = 0 then 0 else Thm2Term n p A (n + m) ξ‖ := by rw [hHe]
      _ ≤ ∑' m : ℕ, ‖(if m = 0 then 0 else Thm2Term n p A (n + m) ξ)‖ :=
          norm_tsum_le_tsum_norm hns2
      _ ≤ ∑' m : ℕ, 4 * CA * ‖ξ‖ ^ b * (1 / 2 : ℝ) ^ m :=
          hns2.tsum_le_tsum hb1 hmajs
      _ = 4 * CA * ‖ξ‖ ^ b * (1 - (1 / 2 : ℝ))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ = 8 * CA * ‖ξ‖ ^ b := by norm_num; ring
  have hqtend : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖ ^ b) (nhds (0 : ℂ)) (nhds 0) := by
    have h1 : ContinuousAt (fun x : ℝ => x ^ b) 0 :=
      Real.continuousAt_rpow_const 0 b (Or.inr hb0.le)
    have h2 : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖) (nhds (0 : ℂ)) (nhds 0) := by
      have hc := (continuous_norm (E := ℂ)).continuousAt (x := (0 : ℂ))
      rw [ContinuousAt, norm_zero] at hc
      exact hc
    have h3 : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖ ^ b) (nhds (0 : ℂ))
        (nhds ((0 : ℝ) ^ b)) := h1.tendsto.comp h2
    rw [Real.zero_rpow (ne_of_gt hb0)] at h3
    exact h3
  have hqtendW : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖ ^ b)
      (nhdsWithin (0 : ℂ) {ξ : ℂ | ‖ξ‖ < 1}) (nhds 0) :=
    hqtend.mono_left nhdsWithin_le_nhds
  have hHcontzero : ContinuousWithinAt H {ξ : ℂ | ‖ξ‖ < 1} 0 := by
    rw [ContinuousWithinAt, hH0, ← tendsto_sub_nhds_zero_iff]
    have hg : Filter.Tendsto (fun ξ : ℂ => 8 * CA * ‖ξ‖ ^ b)
        (nhdsWithin (0 : ℂ) {ξ : ℂ | ‖ξ‖ < 1}) (nhds 0) := by
      have h := hqtendW.const_mul (8 * CA)
      simpa using h
    refine squeeze_zero_norm' ?_ hg
    have hev1 : ∀ᶠ ξ : ℂ in nhdsWithin (0 : ℂ) {ξ : ℂ | ‖ξ‖ < 1}, ‖ξ‖ ^ b ≤ 1 / 2 :=
      hqtendW.eventually_le_const (by norm_num)
    have hev2 : ∀ᶠ ξ : ℂ in nhdsWithin (0 : ℂ) {ξ : ℂ | ‖ξ‖ < 1}, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} :=
      eventually_mem_nhdsWithin
    filter_upwards [hev1, hev2] with ξ h1 h2
    by_cases hξ : ξ = 0
    · rw [hξ, hH0, sub_self, norm_zero]
      positivity
    · exact htail ξ hξ h2 h1
  -- assembling the two halves: continuity within the disc at every point
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]
    exact hHcontzero
  · exact (hHcontne x hx0 hx).continuousWithinAt
