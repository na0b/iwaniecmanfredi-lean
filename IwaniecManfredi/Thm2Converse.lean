import IwaniecManfredi.Thm2SeriesW12Convergence
import IwaniecManfredi.Thm2TermSolvesEq18
import IwaniecManfredi.EnergyIdentity
import IwaniecManfredi.Eq18ImpliesQuasiregular
import IwaniecManfredi.WeakPartialEqFDerivAE

open MeasureTheory

/-- The converse half of Theorem 2: given coefficients `A_k`, `k ≥ n`, with
`Σ_{k≥n} k|A_k|² < ∞`, the series (19) converges in `W^{1,2}(B)` to a solution
of (18) whose energy is at most `C(n,p) Σ_{k≥n+1} k|A_k|²`.  The hypothesis sum
starts at `n` while the bound's starts at `n+1`; that asymmetry is the paper's
own and is correct, since `λ_n = 0` makes the `k = n` summand the constant `A_n`,
which carries no energy.  As in the forward half there is no `K` and no
`p ≠ 2`. -/
theorem Thm2Converse (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : ℤ → ℂ,
        Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) →
        ∃ H : ℂ → ℂ,
          MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H ∧
          ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1} ∧
          ContDiffOn ℝ (⊤ : ℕ∞) H ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) ∧
          SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H ∧
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
            Filter.atTop (nhds 0) ∧
          (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, (‖DZ H ξ‖ ^ 2 + ‖DZbar H ξ‖ ^ 2))
            ≤ C * ∑' m : ℕ, ((n : ℝ) + 1 + (m : ℝ)) * ‖A ((n : ℤ) + 1 + (m : ℤ))‖ ^ 2 := by
  -- ## Step 0: the constant.  `Eq18ImpliesQuasiregular` produces exactly the
  -- paper's `K = max {p-1, 1/(p-1)}`, so `EnergyIdentity` is instantiated at that
  -- `K`; since `K` depends on `p` alone the constant it returns is `C(n, p)`.
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK : (1 : ℝ) ≤ max (p - 1) (1 / (p - 1)) := by
    rcases le_or_gt 2 p with h2 | h2
    · exact le_trans (by linarith) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hp1]
      linarith
  obtain ⟨C, hC0, hEI⟩ := EnergyIdentity n p (max (p - 1) (1 / (p - 1))) hn hp hK
  refine ⟨C, hC0, ?_⟩
  intro A hsum
  -- ## Step 1: the normalised coefficient family `Ã`, which carries the
  -- compatibility relation (39) that `Thm2SeriesW12Convergence` and
  -- `EnergyIdentity` both ask for, and which agrees with `A` from `n` on.
  obtain ⟨At, hAtv⟩ : ∃ At : ℤ → ℂ, ∀ j : ℤ, At j =
      if (n : ℤ) ≤ j then A j
      else if j ≤ -(n : ℤ) then ((EpsCoef n (-j).natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A (-j))
      else 0 := ⟨_, fun _ => rfl⟩
  have hAteq : ∀ j : ℤ, (n : ℤ) ≤ j → At j = A j := by
    intro j hj
    rw [hAtv j, if_pos hj]
  have hAtcomp : ∀ k : ℤ, (n : ℤ) ≤ k →
      At (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (At k) := by
    intro k hk
    have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    rw [hAtv (-k), if_neg (by omega : ¬ ((n : ℤ) ≤ -k)),
      if_pos (by omega : -k ≤ -(n : ℤ)), neg_neg, hAteq k hk]
  have hAtsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖At ((n : ℤ) + (m : ℤ))‖ ^ 2) := by
    refine hsum.congr (fun m => ?_)
    rw [hAteq ((n : ℤ) + (m : ℤ)) (by omega)]
  have hTeq : ∀ k : ℕ, n ≤ k → Thm2Term n p At k = Thm2Term n p A k := by
    intro k hk
    funext ξ
    have h : At (k : ℤ) = A (k : ℤ) := hAteq (k : ℤ) (by exact_mod_cast hk)
    simp only [Thm2Term, h]
  have hSeq : ∀ (N : ℕ) (ξ : ℂ),
      (∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k ξ)
        = ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k ξ := by
    intro N ξ
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hTeq k (Finset.mem_Icc.mp hk).1]
  -- ## Step 2: the sum of the series
  obtain ⟨H, hHcont, hHcd, hHW, hHint, hHfour, hHfour0, hHtend⟩ :=
    Thm2SeriesW12Convergence n p hn hp At hAtcomp hAtsum
  -- ## Step 3: `H` solves (18).
  have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    simp
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hBmin : IsOpen ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    rw [Set.sdiff_eq]
    exact hBopen.inter isOpen_compl_singleton
  have hdiffH : ∀ᵐ z : ℂ, z ∈ {ξ : ℂ | ‖ξ‖ < 1} → DifferentiableAt ℝ H z := by
    filter_upwards [hne0] with z hz0 hzB
    have hmem : z ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := ⟨hzB, by simpa using hz0⟩
    exact ((hHcd.differentiableOn (by simp)) z hmem).differentiableAt (hBmin.mem_nhds hmem)
  -- fact (W): the weak Wirtinger derivatives agree almost everywhere with the
  -- pointwise ones as soon as the function is almost everywhere differentiable.
  have factW : ∀ (u a b : ℂ → ℂ), IsWeakWirtingerOn {ξ : ℂ | ‖ξ‖ < 1} u a b →
      (∀ᵐ z : ℂ, z ∈ {ξ : ℂ | ‖ξ‖ < 1} → DifferentiableAt ℝ u z) →
      ∀ᵐ z : ℂ, z ∈ {ξ : ℂ | ‖ξ‖ < 1} → a z = DZ u z ∧ b z = DZbar u z := by
    intro u a b hww hdiff
    obtain ⟨fx, fy, hu1, hfx1, hfy1, hwx, hwy, ha, hb⟩ := hww
    have hDm : ∀ j : Fin 2,
        MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} ((fun j : Fin 2 => if j = 0 then fx else fy) j) := by
      intro j
      by_cases hj : j = 0
      · simpa [hj] using hfx1
      · simpa [hj] using hfy1
    have hDw : ∀ j : Fin 2, IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} j u
        ((fun j : Fin 2 => if j = 0 then fx else fy) j) := by
      intro j
      by_cases hj : j = 0
      · subst hj
        simpa using hwx
      · have hj1 : j = 1 := by omega
        subst hj1
        simpa using hwy
    have hD := WeakPartialEqFDerivAE {ξ : ℂ | ‖ξ‖ < 1} hBopen u
      (fun j : Fin 2 => if j = 0 then fx else fy) hu1 hDm hDw hdiff
    filter_upwards [hD 0, hD 1] with z h0 h1 hz
    have e0 : fx z = fderiv ℝ u z 1 := by
      have h := h0 hz
      simpa [PartialWord] using h
    have e1 : fy z = fderiv ℝ u z Complex.I := by
      have h := h1 hz
      simpa [PartialWord] using h
    refine ⟨?_, ?_⟩
    · rw [ha z, e0, e1, DZ]
    · rw [hb z, e0, e1, DZbar]
  -- `DZ`, `DZbar` commute with a finite sum wherever every summand is differentiable
  have hDZsum : ∀ (s : Finset ℕ) (f : ℕ → ℂ → ℂ) (ξ : ℂ),
      (∀ k ∈ s, DifferentiableAt ℝ (f k) ξ) →
      DZ (fun z : ℂ => ∑ k ∈ s, f k z) ξ = ∑ k ∈ s, DZ (f k) ξ
      ∧ DZbar (fun z : ℂ => ∑ k ∈ s, f k z) ξ = ∑ k ∈ s, DZbar (f k) ξ := by
    intro s f ξ hd
    obtain ⟨Phi, Psi, hPhi, hPsi⟩ : ∃ Phi Psi : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ,
        (∀ L : ℂ →L[ℝ] ℂ, Phi L = (1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I))
        ∧ (∀ L : ℂ →L[ℝ] ℂ, Psi L = (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) := by
      refine ⟨(1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ))
          - ((1 / 2 : ℂ) * Complex.I) • (ContinuousLinearMap.apply ℝ ℂ Complex.I),
        (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ))
          + ((1 / 2 : ℂ) * Complex.I) • (ContinuousLinearMap.apply ℝ ℂ Complex.I),
        fun L => ?_, fun L => ?_⟩ <;>
        simp [smul_eq_mul] <;> ring
    have he : fderiv ℝ (fun z : ℂ => ∑ k ∈ s, f k z) ξ = ∑ k ∈ s, fderiv ℝ (f k) ξ :=
      (HasFDerivAt.fun_sum (fun k hk => (hd k hk).hasFDerivAt)).fderiv
    have hDZ : ∀ (g : ℂ → ℂ) (z : ℂ),
        DZ g z = Phi (fderiv ℝ g z) ∧ DZbar g z = Psi (fderiv ℝ g z) :=
      fun g z => ⟨(hPhi _).symm, (hPsi _).symm⟩
    constructor
    · rw [(hDZ _ ξ).1, he, map_sum]
      exact Finset.sum_congr rfl (fun k _ => ((hDZ _ ξ).1).symm)
    · rw [(hDZ _ ξ).2, he, map_sum]
      exact Finset.sum_congr rfl (fun k _ => ((hDZ _ ξ).2).symm)
  -- (4): the pointwise form of (18) for a single summand
  have hTkpt : ∀ k : ℕ, n ≤ k → ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → ξ ≠ 0 →
      DZbar (Thm2Term n p At k) ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * DZ (Thm2Term n p At k) ξ
          + ((starRingEnd ℂ ξ) ^ n / ξ ^ n)
              * starRingEnd ℂ (DZ (Thm2Term n p At k) ξ)) := by
    intro k hk
    obtain ⟨ak, bk, hwwk, hidk⟩ := (Thm2TermSolvesEq18 n p hn hp k hk At).2.2
    have hdiffk : ∀ᵐ z : ℂ, z ∈ {ξ : ℂ | ‖ξ‖ < 1} →
        DifferentiableAt ℝ (Thm2Term n p At k) z := by
      filter_upwards [hne0] with z hz0 _
      exact ((Thm2TermSolvesEq18 n p hn hp k hk At).1 z hz0).differentiableAt (by simp)
    filter_upwards [factW _ _ _ hwwk hdiffk, hidk] with ξ h1 h2 hξB hξ0
    rw [← (h1 hξB).1, ← (h1 hξB).2]
    exact h2 hξB hξ0
  -- (5): the same identity for every partial sum
  have hSNpt : ∀ N : ℕ, ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → ξ ≠ 0 →
      DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ
        = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ)
            * DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ
          + ((starRingEnd ℂ ξ) ^ n / ξ ^ n)
              * starRingEnd ℂ
                (DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ)) := by
    intro N
    have hall : ∀ᵐ ξ : ℂ, ∀ k ∈ Finset.Icc n (n + N),
        ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → ξ ≠ 0 →
        DZbar (Thm2Term n p At k) ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
          ((ξ / starRingEnd ℂ ξ) * DZ (Thm2Term n p At k) ξ
            + ((starRingEnd ℂ ξ) ^ n / ξ ^ n)
                * starRingEnd ℂ (DZ (Thm2Term n p At k) ξ)) :=
      (MeasureTheory.ae_ball_iff (Finset.Icc n (n + N)).countable_toSet).mpr
        (fun k hk => hTkpt k (Finset.mem_Icc.mp hk).1)
    filter_upwards [hall, hne0] with ξ h1 hξ0 hξB _
    have hd : ∀ k ∈ Finset.Icc n (n + N), DifferentiableAt ℝ (Thm2Term n p At k) ξ := by
      intro k hk
      exact ((Thm2TermSolvesEq18 n p hn hp k (Finset.mem_Icc.mp hk).1 At).1 ξ
        hξ0).differentiableAt (by simp)
    rw [(hDZsum _ _ ξ hd).1, (hDZsum _ _ ξ hd).2, map_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [h1 k hk hξB hξ0]
  -- the weak Wirtinger pair of `H`, with the `L²`-to-`L¹` Hölder step on compacts
  obtain ⟨a, b, hww⟩ : ∃ a b : ℂ → ℂ, IsWeakWirtingerOn {ξ : ℂ | ‖ξ‖ < 1} H a b := by
    obtain ⟨D, hD0, hDLp, hDweak⟩ := hHW
    have hholder : ∀ g : ℂ → ℂ, MemLpLocOn 2 {ξ : ℂ | ‖ξ‖ < 1} g →
        MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} g := by
      intro g hg K hKA hKcpt
      have h2 : MemLp (K.indicator g) 2 volume := hg K hKA hKcpt
      refine h2.mono_exponent_of_measure_support_ne_top (s := K) ?_ ?_ (by norm_num)
      · intro x hx
        exact Set.indicator_of_notMem hx g
      · exact (hKcpt.measure_lt_top).ne
    refine ⟨fun z => (1 / 2 : ℂ) * (D [0] z - Complex.I * D [1] z),
      fun z => (1 / 2 : ℂ) * (D [0] z + Complex.I * D [1] z),
      D [0], D [1], ?_, ?_, ?_, ?_, ?_, fun z => rfl, fun z => rfl⟩
    · have h := hDLp [] (by simp)
      rw [hD0] at h
      exact hholder _ h
    · exact hholder _ (hDLp [0] (by simp))
    · exact hholder _ (hDLp [1] (by simp))
    · have h := hDweak [] 0 (by simp)
      rwa [hD0] at h
    · have h := hDweak [] 1 (by simp)
      rwa [hD0] at h
  have hwa := factW H a b hww hdiffH
  -- (5′): the `L²` limit of (5) along the partial sums.  The only integrability
  -- fact the step needs is a single one, at the exponent `2 L₀ - 2` where
  -- `L₀ = (p-1)/(n p) ≤ λ_k` for every `k ≥ n+1` (`LambdaEpsEstimates`), so the
  -- per-`k` bounds collapse into one; the `k = n` summand is constant off `0`.
  have h5prime : ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → ξ ≠ 0 →
      DZbar H ξ = ((1 / 2 - 1 / p : ℝ) : ℂ) *
        ((ξ / starRingEnd ℂ ξ) * DZ H ξ
          + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ (DZ H ξ)) := by
    -- ### The monomial class `E s j l ξ = |ξ|^s ξ^j conj(ξ)^l`, which is closed under
    -- `DZ` and `DZbar`: one differentiation drops the total exponent by exactly one.
    obtain ⟨EE, hEEf⟩ : ∃ EE : ℝ → ℤ → ℤ → ℂ → ℂ, ∀ (s : ℝ) (j l : ℤ),
        EE s j l = fun ξ : ℂ => ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l :=
      ⟨fun s j l ξ => ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l, fun _ _ _ => rfl⟩
    have hEEv : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ),
        EE s j l ξ = ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l := by
      intro s j l ξ
      rw [hEEf s j l]
    have zpowcd : ∀ (j : ℤ) (ξ : ℂ), ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ j) ξ := by
      intro j ξ hξ
      rcases le_or_gt 0 j with hj | hj
      · have he : (fun z : ℂ => z ^ j) = (fun z : ℂ => z ^ j.toNat) := by
          funext z
          rw [← zpow_natCast, Int.toNat_of_nonneg hj]
        rw [he]
        exact (contDiff_id.pow j.toNat).contDiffAt
      · obtain ⟨a, ha⟩ : ∃ a : ℕ, j = -(a : ℤ) := ⟨(-j).toNat, by omega⟩
        have he : (fun z : ℂ => z ^ j) = (fun z : ℂ => (z ^ a)⁻¹) := by
          funext z
          rw [ha, zpow_neg, zpow_natCast]
        rw [he]
        exact ((contDiff_id.pow a).contDiffAt).inv (pow_ne_zero _ hξ)
    have zpowcjcd : ∀ (l : ℤ) (ξ : ℂ), ξ ≠ 0 →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => (starRingEnd ℂ z) ^ l) ξ := by
      intro l ξ hξ
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) ξ :=
        Complex.conjCLE.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => w ^ l) (starRingEnd ℂ ξ) :=
        zpowcd l _ (by simpa using hξ)
      exact h2.comp ξ h1
    have EEnorm : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 →
        ‖EE s j l ξ‖ = ‖ξ‖ ^ (s + (j : ℝ) + (l : ℝ)) := by
      intro s j l ξ hξ
      have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      rw [hEEv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hr s), norm_zpow, norm_zpow, Complex.norm_conj,
        ← Real.rpow_intCast ‖ξ‖ j, ← Real.rpow_intCast ‖ξ‖ l,
        ← Real.rpow_add hr, ← Real.rpow_add hr]
    have EEcd : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (EE s j l) ξ := by
      intro s j l ξ hξ
      rw [hEEf s j l]
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ((‖z‖ ^ s : ℝ) : ℂ)) ξ :=
        (WirtingerModulusPowerRule s ξ hξ).1
      exact ((h1.mul (zpowcd j ξ hξ)).mul (zpowcjcd l ξ hξ))
    have EEdiff : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 → DifferentiableAt ℝ (EE s j l) ξ :=
      fun s j l ξ hξ => (EEcd s j l ξ hξ).differentiableAt (by simp)
    have EEDZ : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 →
        DZ (EE s j l) ξ = ((s / 2 + (j : ℝ) : ℝ) : ℂ) * EE s (j - 1) l ξ
        ∧ DZbar (EE s j l) ξ = ((s / 2 + (l : ℝ) : ℝ) : ℂ) * EE s j (l - 1) ξ := by
      intro s j l ξ hξ
      have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
      have hΩ0 : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
      have hcjne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
      have hGd : DifferentiableAt ℝ (fun z : ℂ => ((‖z‖ ^ s : ℝ) : ℂ)) ξ :=
        (WirtingerModulusPowerRule s ξ hξ).1.differentiableAt hone
      have hPd : DifferentiableAt ℝ (fun z : ℂ => z ^ j) ξ :=
        (zpowcd j ξ hξ).differentiableAt hone
      have hQd : DifferentiableAt ℝ (fun z : ℂ => (starRingEnd ℂ z) ^ l) ξ :=
        (zpowcjcd l ξ hξ).differentiableAt hone
      have hDZid : DZ (fun w : ℂ => w) ξ = 1 ∧ DZbar (fun w : ℂ => w) ξ = 0 := by
        have h : fderiv ℝ (fun w : ℂ => w) ξ = ContinuousLinearMap.id ℝ ℂ := fderiv_id
        refine ⟨?_, ?_⟩ <;>
          simp only [DZ, DZbar, h, ContinuousLinearMap.id_apply] <;>
          rw [Complex.I_mul_I] <;> ring
      have hDZconj : DZ (fun w : ℂ => starRingEnd ℂ w) ξ = 0 ∧
          DZbar (fun w : ℂ => starRingEnd ℂ w) ξ = 1 := by
        have h := WirtingerConjRule (fun w : ℂ => w) ξ differentiableAt_id
        exact ⟨by rw [h.1, hDZid.2, map_zero], by rw [h.2, hDZid.1, map_one]⟩
      have hidC : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => z) {z : ℂ | z ≠ 0} :=
        contDiff_id.contDiffOn
      have hidne : ∀ ζ ∈ {z : ℂ | z ≠ 0}, (fun z : ℂ => z) ζ ≠ 0 := fun ζ hζ => hζ
      have hconjC : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) {z : ℂ | z ≠ 0} :=
        Complex.conjCLE.contDiff.contDiffOn
      have hconjne : ∀ ζ ∈ {z : ℂ | z ≠ 0}, (fun z : ℂ => starRingEnd ℂ z) ζ ≠ 0 := by
        intro ζ hζ
        simpa using hζ
      have hP := WirtingerPowerRule (fun z : ℂ => z) {z : ℂ | z ≠ 0} hΩ0 hidC hidne j ξ hξ
      have hQ := WirtingerPowerRule (fun z : ℂ => starRingEnd ℂ z) {z : ℂ | z ≠ 0} hΩ0 hconjC
        hconjne l ξ hξ
      have hG := WirtingerModulusPowerRule s ξ hξ
      have hGP := WirtingerProductRule (fun z : ℂ => ((‖z‖ ^ s : ℝ) : ℂ))
        (fun z : ℂ => z ^ j) ξ hGd hPd
      have hall := WirtingerProductRule
        (fun z : ℂ => ((‖z‖ ^ s : ℝ) : ℂ) * z ^ j)
        (fun z : ℂ => (starRingEnd ℂ z) ^ l) ξ (hGd.mul hPd) hQd
      have hjm : (ξ : ℂ) ^ (j - 1) = ξ ^ j * ξ⁻¹ := zpow_sub_one₀ hξ j
      have hlm : (starRingEnd ℂ ξ) ^ (l - 1) = (starRingEnd ℂ ξ) ^ l * (starRingEnd ℂ ξ)⁻¹ :=
        zpow_sub_one₀ hcjne l
      constructor
      · rw [hEEf s j l]
        rw [hall.1, hGP.1, hG.2.1, hP.1, hQ.1, hDZid.1, hDZconj.1, hEEv s (j - 1) l ξ,
      hjm]
        push_cast
        field_simp
        ring
      · rw [hEEf s j l]
        rw [hall.2, hGP.2, hG.2.2, hP.2, hQ.2, hDZid.2, hDZconj.2, hEEv s j (l - 1) ξ,
      hlm]
        push_cast
        field_simp
        ring
    have DZcongr : ∀ (f g : ℂ → ℂ) (ξ : ℂ), ξ ≠ 0 → (∀ z : ℂ, z ≠ 0 → f z = g z) →
        DZ f ξ = DZ g ξ ∧ DZbar f ξ = DZbar g ξ := by
      intro f g ξ hξ h
      have hfd : fderiv ℝ f ξ = fderiv ℝ g ξ :=
        Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hξ) h)
      exact ⟨by simp only [DZ, hfd], by simp only [DZbar, hfd]⟩
    have DZlin : ∀ (c1 c2 : ℂ) (f g : ℂ → ℂ) (ξ : ℂ),
        DifferentiableAt ℝ f ξ → DifferentiableAt ℝ g ξ →
        DZ (fun z : ℂ => c1 * f z + c2 * g z) ξ = c1 * DZ f ξ + c2 * DZ g ξ
        ∧ DZbar (fun z : ℂ => c1 * f z + c2 * g z) ξ = c1 * DZbar f ξ + c2 * DZbar g ξ := by
      intro c1 c2 f g ξ hf hg
      have h : fderiv ℝ (fun z : ℂ => c1 * f z + c2 * g z) ξ
          = c1 • fderiv ℝ f ξ + c2 • fderiv ℝ g ξ :=
        ((hf.hasFDerivAt.const_mul c1).fun_add (hg.hasFDerivAt.const_mul c2)).fderiv
      refine ⟨?_, ?_⟩ <;>
        simp only [DZ, DZbar, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] <;>
        ring
    have Trep : ∀ (k : ℕ) (z : ℂ), z ≠ 0 →
        Thm2Term n p At k z
          = At (k : ℤ) * EE (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) ((k : ℤ) - (n : ℤ)) 0 z
            + (((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (At (k : ℤ)))
                * EE (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) (-(n : ℤ)) (k : ℤ) z := by
      intro k z hz
      have hcj : starRingEnd ℂ z ≠ 0 := by simpa using hz
      rw [hEEv, hEEv, Thm2Term, zpow_sub₀ hz, zpow_neg, zpow_zero, zpow_natCast, zpow_natCast,
        zpow_natCast]
      field_simp
    have DZTbd : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ z : ℂ, z ≠ 0 →
        ‖DZ (Thm2Term n p At k) z‖ ≤ Ck * ‖z‖ ^ (LambdaCoef n k p - 1)
        ∧ ‖DZbar (Thm2Term n p At k) z‖ ≤ Ck * ‖z‖ ^ (LambdaCoef n k p - 1) := by
      intro k
      set s : ℝ := LambdaCoef n k p + (n : ℝ) - (k : ℝ) with hs
      obtain ⟨c1, hc1⟩ : ∃ c : ℂ, c = At (k : ℤ) := ⟨_, rfl⟩
      obtain ⟨c2, hc2⟩ : ∃ c : ℂ,
          c = ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (At (k : ℤ)) := ⟨_, rfl⟩
      refine ⟨‖c1‖ * (|s / 2 + ((k : ℝ) - (n : ℝ))| + |s / 2|)
          + ‖c2‖ * (|s / 2 - (n : ℝ)| + |s / 2 + (k : ℝ)|), by positivity, ?_⟩
      intro z hz
      have hd1 : DifferentiableAt ℝ (EE s ((k : ℤ) - (n : ℤ)) 0) z := EEdiff s _ _ z hz
      have hd2 : DifferentiableAt ℝ (EE s (-(n : ℤ)) (k : ℤ)) z := EEdiff s _ _ z hz
      have hcong := DZcongr (Thm2Term n p At k)
        (fun w : ℂ => c1 * EE s ((k : ℤ) - (n : ℤ)) 0 w + c2 * EE s (-(n : ℤ)) (k : ℤ) w) z hz
        (fun w hw => by rw [hc1, hc2]; exact Trep k w hw)
      have hlin := DZlin c1 c2 (EE s ((k : ℤ) - (n : ℤ)) 0) (EE s (-(n : ℤ)) (k : ℤ)) z hd1 hd2
      have he1 := EEDZ s ((k : ℤ) - (n : ℤ)) 0 z hz
      have he2 := EEDZ s (-(n : ℤ)) (k : ℤ) z hz
      have hpw : (0 : ℝ) ≤ ‖z‖ ^ (LambdaCoef n k p - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have hn1 : ‖EE s ((k : ℤ) - (n : ℤ) - 1) 0 z‖ = ‖z‖ ^ (LambdaCoef n k p - 1) := by
        rw [EEnorm s _ _ z hz, hs]
        push_cast
        ring_nf
      have hn2 : ‖EE s (-(n : ℤ) - 1) (k : ℤ) z‖ = ‖z‖ ^ (LambdaCoef n k p - 1) := by
        rw [EEnorm s _ _ z hz, hs]
        push_cast
        ring_nf
      have hn3 : ‖EE s ((k : ℤ) - (n : ℤ)) (0 - 1) z‖ = ‖z‖ ^ (LambdaCoef n k p - 1) := by
        rw [EEnorm s _ _ z hz, hs]
        push_cast
        ring_nf
      have hn4 : ‖EE s (-(n : ℤ)) ((k : ℤ) - 1) z‖ = ‖z‖ ^ (LambdaCoef n k p - 1) := by
        rw [EEnorm s _ _ z hz, hs]
        push_cast
        ring_nf
      have hcast1 : ‖((s / 2 + (((k : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)‖
          = |s / 2 + ((k : ℝ) - (n : ℝ))| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        push_cast
        ring_nf
      have hcast2 : ‖((s / 2 + ((0 : ℤ) : ℝ) : ℝ) : ℂ)‖ = |s / 2| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        push_cast
        ring_nf
      have hcast3 : ‖((s / 2 + ((-(n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)‖ = |s / 2 - (n : ℝ)| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        push_cast
        ring_nf
      have hcast4 : ‖((s / 2 + (((k : ℕ) : ℤ) : ℝ) : ℝ) : ℂ)‖ = |s / 2 + (k : ℝ)| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        push_cast
        ring_nf
      constructor
      · rw [hcong.1, hlin.1, he1.1, he2.1]
        calc ‖c1 * (((s / 2 + (((k : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s ((k : ℤ) - (n : ℤ) - 1) 0 z)
                + c2 * (((s / 2 + ((-(n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s (-(n : ℤ) - 1) (k : ℤ) z)‖
            ≤ ‖c1 * (((s / 2 + (((k : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s ((k : ℤ) - (n : ℤ) - 1) 0 z)‖
                + ‖c2 * (((s / 2 + ((-(n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s (-(n : ℤ) - 1) (k : ℤ) z)‖ := norm_add_le _ _
          _ = ‖c1‖ * |s / 2 + ((k : ℝ) - (n : ℝ))| * ‖z‖ ^ (LambdaCoef n k p - 1)
                + ‖c2‖ * |s / 2 - (n : ℝ)| * ‖z‖ ^ (LambdaCoef n k p - 1) := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, hcast1, hcast3, hn1, hn2]
              ring
          _ ≤ (‖c1‖ * (|s / 2 + ((k : ℝ) - (n : ℝ))| + |s / 2|)
                + ‖c2‖ * (|s / 2 - (n : ℝ)| + |s / 2 + (k : ℝ)|))
                * ‖z‖ ^ (LambdaCoef n k p - 1) := by
              have h1 : (0 : ℝ) ≤ ‖c1‖ := norm_nonneg _
              have h2 : (0 : ℝ) ≤ ‖c2‖ := norm_nonneg _
              have h3 : (0 : ℝ) ≤ |s / 2| := abs_nonneg _
              have h4 : (0 : ℝ) ≤ |s / 2 + (k : ℝ)| := abs_nonneg _
              have hA : ‖c1‖ * |s / 2 + ((k : ℝ) - (n : ℝ))|
                  ≤ ‖c1‖ * (|s / 2 + ((k : ℝ) - (n : ℝ))| + |s / 2|) := by
                refine mul_le_mul_of_nonneg_left (by linarith) h1
              have hB : ‖c2‖ * |s / 2 - (n : ℝ)|
                  ≤ ‖c2‖ * (|s / 2 - (n : ℝ)| + |s / 2 + (k : ℝ)|) := by
                refine mul_le_mul_of_nonneg_left (by linarith) h2
              have := mul_le_mul_of_nonneg_right (add_le_add hA hB) hpw
              calc ‖c1‖ * |s / 2 + ((k : ℝ) - (n : ℝ))| * ‖z‖ ^ (LambdaCoef n k p - 1)
                    + ‖c2‖ * |s / 2 - (n : ℝ)| * ‖z‖ ^ (LambdaCoef n k p - 1)
                  = (‖c1‖ * |s / 2 + ((k : ℝ) - (n : ℝ))|
                      + ‖c2‖ * |s / 2 - (n : ℝ)|) * ‖z‖ ^ (LambdaCoef n k p - 1) := by ring
                _ ≤ _ := this
      · rw [hcong.2, hlin.2, he1.2, he2.2]
        calc ‖c1 * (((s / 2 + ((0 : ℤ) : ℝ) : ℝ) : ℂ) * EE s ((k : ℤ) - (n : ℤ)) (0 - 1) z)
                + c2 * (((s / 2 + (((k : ℕ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s (-(n : ℤ)) ((k : ℤ) - 1) z)‖
            ≤ ‖c1 * (((s / 2 + ((0 : ℤ) : ℝ) : ℝ) : ℂ) * EE s ((k : ℤ) - (n : ℤ)) (0 - 1) z)‖
                + ‖c2 * (((s / 2 + (((k : ℕ) : ℤ) : ℝ) : ℝ) : ℂ)
                  * EE s (-(n : ℤ)) ((k : ℤ) - 1) z)‖ := norm_add_le _ _
          _ = ‖c1‖ * |s / 2| * ‖z‖ ^ (LambdaCoef n k p - 1)
                + ‖c2‖ * |s / 2 + (k : ℝ)| * ‖z‖ ^ (LambdaCoef n k p - 1) := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, hcast2, hcast4, hn3, hn4]
              ring
          _ ≤ (‖c1‖ * (|s / 2 + ((k : ℝ) - (n : ℝ))| + |s / 2|)
                + ‖c2‖ * (|s / 2 - (n : ℝ)| + |s / 2 + (k : ℝ)|))
                * ‖z‖ ^ (LambdaCoef n k p - 1) := by
              have h1 : (0 : ℝ) ≤ ‖c1‖ := norm_nonneg _
              have h2 : (0 : ℝ) ≤ ‖c2‖ := norm_nonneg _
              have h3 : (0 : ℝ) ≤ |s / 2 + ((k : ℝ) - (n : ℝ))| := abs_nonneg _
              have h4 : (0 : ℝ) ≤ |s / 2 - (n : ℝ)| := abs_nonneg _
              have hA : ‖c1‖ * |s / 2| ≤ ‖c1‖ * (|s / 2 + ((k : ℝ) - (n : ℝ))| + |s / 2|) :=
                mul_le_mul_of_nonneg_left (by linarith) h1
              have hB : ‖c2‖ * |s / 2 + (k : ℝ)|
                  ≤ ‖c2‖ * (|s / 2 - (n : ℝ)| + |s / 2 + (k : ℝ)|) :=
                mul_le_mul_of_nonneg_left (by linarith) h2
              have := mul_le_mul_of_nonneg_right (add_le_add hA hB) hpw
              calc ‖c1‖ * |s / 2| * ‖z‖ ^ (LambdaCoef n k p - 1)
                    + ‖c2‖ * |s / 2 + (k : ℝ)| * ‖z‖ ^ (LambdaCoef n k p - 1)
                  = (‖c1‖ * |s / 2| + ‖c2‖ * |s / 2 + (k : ℝ)|)
                      * ‖z‖ ^ (LambdaCoef n k p - 1) := by ring
                _ ≤ _ := this
    have DZTn : ∀ z : ℂ, z ≠ 0 →
        DZ (Thm2Term n p At n) z = 0 ∧ DZbar (Thm2Term n p At n) z = 0 := by
      intro z hz
      obtain ⟨hlamn, hepsn, -, -⟩ := LambdaEpsEstimates n p hn hp
      have hconst : ∀ w : ℂ, w ≠ 0 → Thm2Term n p At n w = At (n : ℤ) := by
        intro w hw
        rw [Thm2Term, hlamn, hepsn]
        have h0 : ((0 : ℝ) + (n : ℝ) - (n : ℝ)) = 0 := by ring
        rw [h0, Real.rpow_zero]
        push_cast
        rw [zpow_neg, zpow_natCast]
        field_simp
        ring
      have h := DZcongr (Thm2Term n p At n) (fun _ : ℂ => At (n : ℤ)) z hz hconst
      rw [h.1, h.2, DZ, DZbar]
      simp
    have Sbd : ∀ N : ℕ, ∃ CN : ℝ, 0 ≤ CN ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
        ‖DZ (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) z‖
            ≤ CN * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1)
        ∧ ‖DZbar (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) z‖
            ≤ CN * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := by
      intro N
      obtain ⟨-, -, -, hlam⟩ := LambdaEpsEstimates n p hn hp
      choose Cf hCf0 hCfbd using fun k : ℕ => DZTbd k
      refine ⟨∑ k ∈ Finset.Icc (n + 1) (n + N), Cf k,
        Finset.sum_nonneg (fun k _ => hCf0 k), ?_⟩
      intro z hz hz1
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hd : ∀ k ∈ Finset.Icc n (n + N), DifferentiableAt ℝ (Thm2Term n p At k) z := by
        intro k hk
        exact ((Thm2TermSolvesEq18 n p hn hp k (Finset.mem_Icc.mp hk).1 At).1 z
          hz).differentiableAt (by simp)
      have hsplit : Finset.Icc n (n + N) = insert n (Finset.Icc (n + 1) (n + N)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : n ∉ Finset.Icc (n + 1) (n + N) := by simp
      have hbd1 : ∀ k ∈ Finset.Icc (n + 1) (n + N),
          ‖DZ (Thm2Term n p At k) z‖ ≤ Cf k * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := by
        intro k hk
        refine le_trans (hCfbd k z hz).1 (mul_le_mul_of_nonneg_left ?_ (hCf0 k))
        exact Real.rpow_le_rpow_of_exponent_ge hzpos hz1
          (by linarith [(hlam k (Finset.mem_Icc.mp hk).1).1])
      have hbd2 : ∀ k ∈ Finset.Icc (n + 1) (n + N),
          ‖DZbar (Thm2Term n p At k) z‖ ≤ Cf k * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := by
        intro k hk
        refine le_trans (hCfbd k z hz).2 (mul_le_mul_of_nonneg_left ?_ (hCf0 k))
        exact Real.rpow_le_rpow_of_exponent_ge hzpos hz1
          (by linarith [(hlam k (Finset.mem_Icc.mp hk).1).1])
      constructor
      · rw [(hDZsum _ _ z hd).1, hsplit, Finset.sum_insert hnotmem,
          (DZTn z hz).1, zero_add]
        calc ‖∑ k ∈ Finset.Icc (n + 1) (n + N), DZ (Thm2Term n p At k) z‖
            ≤ ∑ k ∈ Finset.Icc (n + 1) (n + N), ‖DZ (Thm2Term n p At k) z‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.Icc (n + 1) (n + N),
                Cf k * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := Finset.sum_le_sum hbd1
          _ = (∑ k ∈ Finset.Icc (n + 1) (n + N), Cf k)
                * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := by rw [← Finset.sum_mul]
      · rw [(hDZsum _ _ z hd).2, hsplit, Finset.sum_insert hnotmem,
          (DZTn z hz).2, zero_add]
        calc ‖∑ k ∈ Finset.Icc (n + 1) (n + N), DZbar (Thm2Term n p At k) z‖
            ≤ ∑ k ∈ Finset.Icc (n + 1) (n + N), ‖DZbar (Thm2Term n p At k) z‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.Icc (n + 1) (n + N),
                Cf k * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := Finset.sum_le_sum hbd2
          _ = (∑ k ∈ Finset.Icc (n + 1) (n + N), Cf k)
                * ‖z‖ ^ ((p - 1) / ((n : ℝ) * p) - 1) := by rw [← Finset.sum_mul]
    have DZmeas : ∀ f : ℂ → ℂ, Measurable (DZ f) ∧ Measurable (DZbar f) := by
      intro f
      have h1 := measurable_fderiv_apply_const ℝ f (1 : ℂ)
      have h2 := measurable_fderiv_apply_const ℝ f Complex.I
      have e1 : DZ f = fun z : ℂ =>
          (1 / 2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) := rfl
      have e2 : DZbar f = fun z : ℂ =>
          (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) := rfl
      refine ⟨?_, ?_⟩
      · rw [e1]
        exact (h1.sub (h2.const_mul _)).const_mul _
      · rw [e2]
        exact (h1.add (h2.const_mul _)).const_mul _
    have IntL0 : IntegrableOn (fun ξ : ℂ => ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2))
        {ξ : ℂ | ‖ξ‖ < 1} volume := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hL0 : 0 < (p - 1) / ((n : ℝ) * p) := by
        refine div_pos (by linarith) ?_
        have : (0 : ℝ) < p := by linarith
        positivity
      have hα0 : 0 < min (2 * ((p - 1) / ((n : ℝ) * p))) 1 := lt_min (by linarith) one_pos
      have hα1 : min (2 * ((p - 1) / ((n : ℝ) * p))) 1 ≤ 1 := min_le_right _ _
      have hq2 : (1 : ℝ) < 2 / (2 - min (2 * ((p - 1) / ((n : ℝ) * p))) 1) := by
        rw [lt_div_iff₀ (by linarith)]
        linarith
      have hpi := PowerIntegrableNearZero (min (2 * ((p - 1) / ((n : ℝ) * p))) 1) hα0 hα1
        1 one_pos 1 le_rfl hq2
      rw [mul_one] at hpi
      have hballeq : Metric.ball (0 : ℂ) 1 = {ξ : ℂ | ‖ξ‖ < 1} := by
        ext ξ
        simp [Metric.mem_ball, dist_eq_norm]
      rw [hballeq] at hpi
      have hBmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} :=
        (isOpen_lt continuous_norm continuous_const).measurableSet
      have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
        refine (MeasureTheory.ae_iff).mpr ?_
        simp
      refine hpi.mono' ((continuous_norm.measurable.pow measurable_const).aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
        MeasureTheory.ae_restrict_mem hBmeas] with ξ hξ0 hξB
      have hzpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
      have hz1 : ‖ξ‖ ≤ 1 := le_of_lt hξB
      have hnn : (0 : ℝ) ≤ ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2) :=
        Real.rpow_nonneg (norm_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact Real.rpow_le_rpow_of_exponent_ge hzpos hz1
        (by have := min_le_left (2 * ((p - 1) / ((n : ℝ) * p))) 1; linarith)
    have IntDZS : ∀ N : ℕ, IntegrableOn (fun ξ : ℂ =>
          ‖DZ (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) ξ‖ ^ 2)
        {ξ : ℂ | ‖ξ‖ < 1} volume
      ∧ IntegrableOn (fun ξ : ℂ =>
          ‖DZbar (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) ξ‖ ^ 2)
        {ξ : ℂ | ‖ξ‖ < 1} volume := by
      intro N
      obtain ⟨CN, hCN0, hCN⟩ := Sbd N
      have hBmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} :=
        (isOpen_lt continuous_norm continuous_const).measurableSet
      have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
        refine (MeasureTheory.ae_iff).mpr ?_
        simp
      have hint : IntegrableOn (fun ξ : ℂ =>
          CN ^ 2 * ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2)) {ξ : ℂ | ‖ξ‖ < 1} volume :=
        (IntL0).const_mul _
      have hpow : ∀ ξ : ℂ, (‖ξ‖ ^ ((p - 1) / ((n : ℝ) * p) - 1)) ^ 2
          = ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2) := by
        intro ξ
        rw [← Real.rpow_natCast (‖ξ‖ ^ ((p - 1) / ((n : ℝ) * p) - 1)) 2,
          ← Real.rpow_mul (norm_nonneg _)]
        push_cast
        ring_nf
      constructor
      · refine hint.mono' (((DZmeas _).1.norm.pow_const 2).aestronglyMeasurable) ?_
        filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
          MeasureTheory.ae_restrict_mem hBmeas] with ξ hξ0 hξB
        have hb := (hCN ξ hξ0 (le_of_lt hξB)).1
        have hnn : (0 : ℝ) ≤ ‖DZ (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N),
            Thm2Term n p At k w) ξ‖ ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        calc ‖DZ (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) ξ‖ ^ 2
            ≤ (CN * ‖ξ‖ ^ ((p - 1) / ((n : ℝ) * p) - 1)) ^ 2 := by
              refine pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = CN ^ 2 * ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2) := by
              rw [mul_pow, hpow]
      · refine hint.mono' (((DZmeas _).2.norm.pow_const 2).aestronglyMeasurable) ?_
        filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
          MeasureTheory.ae_restrict_mem hBmeas] with ξ hξ0 hξB
        have hb := (hCN ξ hξ0 (le_of_lt hξB)).2
        have hnn : (0 : ℝ) ≤ ‖DZbar (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N),
            Thm2Term n p At k w) ξ‖ ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        calc ‖DZbar (fun w : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k w) ξ‖ ^ 2
            ≤ (CN * ‖ξ‖ ^ ((p - 1) / ((n : ℝ) * p) - 1)) ^ 2 := by
              refine pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = CN ^ 2 * ‖ξ‖ ^ (2 * ((p - 1) / ((n : ℝ) * p)) - 2) := by
              rw [mul_pow, hpow]
    have IntSub : ∀ (u v : ℂ → ℂ), Measurable u → Measurable v →
        IntegrableOn (fun ξ : ℂ => ‖u ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume →
        IntegrableOn (fun ξ : ℂ => ‖v ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume →
        IntegrableOn (fun ξ : ℂ => ‖u ξ - v ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume := by
      intro u v hu hv hiu hiv
      have hint : IntegrableOn (fun ξ : ℂ => 2 * ‖u ξ‖ ^ 2 + 2 * ‖v ξ‖ ^ 2)
          {ξ : ℂ | ‖ξ‖ < 1} volume := (hiu.const_mul 2).add (hiv.const_mul 2)
      refine hint.mono' (((hu.sub hv).norm.pow_const 2).aestronglyMeasurable) ?_
      filter_upwards with ξ
      have h1 : ‖u ξ - v ξ‖ ≤ ‖u ξ‖ + ‖v ξ‖ := norm_sub_le _ _
      have h2 : (0 : ℝ) ≤ ‖u ξ‖ := norm_nonneg _
      have h3 : (0 : ℝ) ≤ ‖v ξ‖ := norm_nonneg _
      have hnn : (0 : ℝ) ≤ ‖u ξ - v ξ‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc ‖u ξ - v ξ‖ ^ 2 ≤ (‖u ξ‖ + ‖v ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * ‖u ξ‖ ^ 2 + 2 * ‖v ξ‖ ^ 2 := by nlinarith [sq_nonneg (‖u ξ‖ - ‖v ξ‖)]
    have hBmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} :=
      (isOpen_lt continuous_norm continuous_const).measurableSet
    -- the two halves of the energy are separately integrable
    have hDZH : IntegrableOn (fun ξ : ℂ => ‖DZ H ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume := by
      refine hHint.mono' (((DZmeas H).1.norm.pow_const 2).aestronglyMeasurable) ?_
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖DZ H ξ‖ ^ 2)]
      linarith [pow_two_nonneg ‖DZbar H ξ‖]
    have hDZbarH : IntegrableOn (fun ξ : ℂ => ‖DZbar H ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume := by
      refine hHint.mono' (((DZmeas H).2.norm.pow_const 2).aestronglyMeasurable) ?_
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖DZbar H ξ‖ ^ 2)]
      linarith [pow_two_nonneg ‖DZ H ξ‖]
    -- the coefficient map of (18) and its two properties
    obtain ⟨Phi, hPhi⟩ : ∃ Phi : ℂ → ℂ → ℂ, ∀ ξ w : ℂ, Phi ξ w =
        ((1 / 2 - 1 / p : ℝ) : ℂ) * ((ξ / starRingEnd ℂ ξ) * w
          + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ w) := ⟨_, fun _ _ => rfl⟩
    have hPhisub : ∀ ξ w1 w2 : ℂ, Phi ξ (w1 - w2) = Phi ξ w1 - Phi ξ w2 := by
      intro ξ w1 w2
      rw [hPhi, hPhi, hPhi, map_sub]
      ring
    have hPhinorm : ∀ ξ w : ℂ, ξ ≠ 0 → ‖Phi ξ w‖ ≤ 2 * |1 / 2 - 1 / p| * ‖w‖ := by
      intro ξ w hξ
      have hnz : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
      have h1 : ‖ξ / starRingEnd ℂ ξ‖ = 1 := by
        rw [norm_div, Complex.norm_conj, div_self hnz]
      have h2 : ‖(starRingEnd ℂ ξ) ^ n / ξ ^ n‖ = 1 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_conj, div_self (pow_ne_zero n hnz)]
      rw [hPhi, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |1 / 2 - 1 / p| * ‖(ξ / starRingEnd ℂ ξ) * w
              + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ w‖
          ≤ |1 / 2 - 1 / p| * (‖(ξ / starRingEnd ℂ ξ) * w‖
              + ‖((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ w‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
        _ = |1 / 2 - 1 / p| * (‖w‖ + ‖w‖) := by
            rw [norm_mul, norm_mul, h1, h2, Complex.norm_conj]
            ring
        _ = 2 * |1 / 2 - 1 / p| * ‖w‖ := by ring
    -- the defect `F`
    obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, ∀ ξ : ℂ, F ξ = DZbar H ξ - Phi ξ (DZ H ξ) :=
      ⟨_, fun _ => rfl⟩
    have hFmeas : Measurable F := by
      have h1 : Measurable (fun ξ : ℂ => ξ / starRingEnd ℂ ξ) :=
        measurable_id.div (Complex.continuous_conj.measurable)
      have h2 : Measurable (fun ξ : ℂ => (starRingEnd ℂ ξ) ^ n / ξ ^ n) :=
        ((Complex.continuous_conj.measurable).pow_const n).div (measurable_id.pow_const n)
      have h3 := (DZmeas H).1
      have h4 := (DZmeas H).2
      have he : F = fun ξ : ℂ => DZbar H ξ - ((1 / 2 - 1 / p : ℝ) : ℂ) *
          ((ξ / starRingEnd ℂ ξ) * DZ H ξ
            + ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * starRingEnd ℂ (DZ H ξ)) := by
        funext ξ
        rw [hF, hPhi]
      rw [he]
      exact h4.sub (((h1.mul h3).add
        (h2.mul ((Complex.continuous_conj.measurable).comp h3))).const_mul _)
    have hFint : IntegrableOn (fun ξ : ℂ => ‖F ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume := by
      have hint : IntegrableOn (fun ξ : ℂ => 2 * ‖DZbar H ξ‖ ^ 2
          + 2 * (2 * |1 / 2 - 1 / p|) ^ 2 * ‖DZ H ξ‖ ^ 2) {ξ : ℂ | ‖ξ‖ < 1} volume :=
        (hDZbarH.const_mul 2).add (hDZH.const_mul _)
      refine hint.mono' ((hFmeas.norm.pow_const 2).aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne0] with ξ hξ0
      have hb : ‖F ξ‖ ≤ ‖DZbar H ξ‖ + 2 * |1 / 2 - 1 / p| * ‖DZ H ξ‖ := by
        rw [hF]
        have e1 := norm_sub_le (DZbar H ξ) (Phi ξ (DZ H ξ))
        have e2 := hPhinorm ξ (DZ H ξ) hξ0
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖F ξ‖ ^ 2)]
      have h0 : (0 : ℝ) ≤ ‖DZbar H ξ‖ := norm_nonneg _
      have h1 : (0 : ℝ) ≤ 2 * |1 / 2 - 1 / p| * ‖DZ H ξ‖ := by positivity
      calc ‖F ξ‖ ^ 2 ≤ (‖DZbar H ξ‖ + 2 * |1 / 2 - 1 / p| * ‖DZ H ξ‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ ≤ 2 * ‖DZbar H ξ‖ ^ 2 + 2 * (2 * |1 / 2 - 1 / p|) ^ 2 * ‖DZ H ξ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖DZbar H ξ‖ - 2 * |1 / 2 - 1 / p| * ‖DZ H ξ‖)]
    -- the per-`N` estimate
    have hkey : ∀ N : ℕ, (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖F ξ‖ ^ 2)
        ≤ 2 * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
              - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
          + 2 * (2 * |1 / 2 - 1 / p|) ^ 2
              * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZ H ξ
                  - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N),
                      Thm2Term n p At k z) ξ‖ ^ 2) := by
      intro N
      obtain ⟨hIDZ, hIDZbar⟩ := IntDZS N
      have hsub1 : IntegrableOn (fun ξ : ℂ => ‖DZ H ξ
          - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
          {ξ : ℂ | ‖ξ‖ < 1} volume :=
        IntSub _ _ (DZmeas H).1 (DZmeas _).1 hDZH hIDZ
      have hsub2 : IntegrableOn (fun ξ : ℂ => ‖DZbar H ξ
          - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
          {ξ : ℂ | ‖ξ‖ < 1} volume :=
        IntSub _ _ (DZmeas H).2 (DZmeas _).2 hDZbarH hIDZbar
      have hsplit : (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1},
            (2 * ‖DZbar H ξ
                - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2
              + 2 * (2 * |1 / 2 - 1 / p|) ^ 2 * ‖DZ H ξ
                - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2))
          = 2 * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
                - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
            + 2 * (2 * |1 / 2 - 1 / p|) ^ 2
                * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZ H ξ
                    - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N),
                        Thm2Term n p At k z) ξ‖ ^ 2) := by
        rw [MeasureTheory.integral_add (hsub2.const_mul 2)
            (hsub1.const_mul (2 * (2 * |1 / 2 - 1 / p|) ^ 2)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [← hsplit]
      refine MeasureTheory.integral_mono_of_nonneg ?_
        ((hsub2.const_mul 2).add (hsub1.const_mul (2 * (2 * |1 / 2 - 1 / p|) ^ 2))) ?_
      · filter_upwards with ξ
        positivity
      · filter_upwards [MeasureTheory.ae_restrict_of_ae hne0,
          MeasureTheory.ae_restrict_mem hBmeas,
          MeasureTheory.ae_restrict_of_ae (hSNpt N)] with ξ hξ0 hξB hid
        have hSN : DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ
            = Phi ξ (DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ) := by
          rw [hPhi]
          exact hid hξB hξ0
        have hFeq : F ξ
            = (DZbar H ξ
                - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ)
              - Phi ξ (DZ H ξ
                - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ) := by
          rw [hF, hPhisub, hSN]
          ring
        have hb : ‖F ξ‖
            ≤ ‖DZbar H ξ
                - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖
              + 2 * |1 / 2 - 1 / p| * ‖DZ H ξ
                - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ := by
          rw [hFeq]
          have e1 := norm_sub_le (DZbar H ξ
              - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ)
            (Phi ξ (DZ H ξ
              - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ))
          have e2 := hPhinorm ξ (DZ H ξ
            - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ) hξ0
          linarith
        have h0 : (0 : ℝ) ≤ ‖DZbar H ξ
            - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ :=
          norm_nonneg _
        have h1 : (0 : ℝ) ≤ 2 * |1 / 2 - 1 / p| * ‖DZ H ξ
            - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ := by
          positivity
        calc ‖F ξ‖ ^ 2
            ≤ (‖DZbar H ξ
                  - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖
                + 2 * |1 / 2 - 1 / p| * ‖DZ H ξ
                  - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N),
                      Thm2Term n p At k z) ξ‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ ≤ 2 * ‖DZbar H ξ
                  - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2
                + 2 * (2 * |1 / 2 - 1 / p|) ^ 2 * ‖DZ H ξ
                  - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N),
                      Thm2Term n p At k z) ξ‖ ^ 2 := by
              nlinarith [sq_nonneg (‖DZbar H ξ
                  - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖
                - 2 * |1 / 2 - 1 / p| * ‖DZ H ξ
                  - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖)]
    -- each of the three integrals of (g) tends to `0`
    have hnn : ∀ (g : ℂ → ℂ), 0 ≤ ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖g ξ‖ ^ 2 := fun g =>
      MeasureTheory.setIntegral_nonneg hBmeas (fun x _ => by positivity)
    have hI2 : Filter.Tendsto (fun N : ℕ => ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZ H ξ
        - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun N => hnn _) (fun N => ?_) hHtend
      have a1 := hnn (fun ξ : ℂ => H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k ξ)
      have a3 := hnn (fun ξ : ℂ => DZbar H ξ
        - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ)
      linarith
    have hI3 : Filter.Tendsto (fun N : ℕ => ∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
        - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun N => hnn _) (fun N => ?_) hHtend
      have a1 := hnn (fun ξ : ℂ => H ξ - ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k ξ)
      have a2 := hnn (fun ξ : ℂ => DZ H ξ
        - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ)
      linarith
    have hlim : Filter.Tendsto (fun N : ℕ =>
        2 * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZbar H ξ
              - DZbar (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z) ξ‖ ^ 2)
          + 2 * (2 * |1 / 2 - 1 / p|) ^ 2
              * (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖DZ H ξ
                  - DZ (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N),
                      Thm2Term n p At k z) ξ‖ ^ 2)) Filter.atTop (nhds 0) := by
      have h1 := hI3.const_mul 2
      have h2 := hI2.const_mul (2 * (2 * |1 / 2 - 1 / p|) ^ 2)
      have h3 := h1.add h2
      rwa [mul_zero, mul_zero, add_zero] at h3
    have hle : (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖F ξ‖ ^ 2) ≤ 0 :=
      ge_of_tendsto hlim (Filter.Eventually.of_forall hkey)
    have hzero : (∫ ξ in {ξ : ℂ | ‖ξ‖ < 1}, ‖F ξ‖ ^ 2) = 0 := le_antisymm hle (hnn F)
    have hae0 : (fun ξ : ℂ => ‖F ξ‖ ^ 2) =ᵐ[volume.restrict {ξ : ℂ | ‖ξ‖ < 1}] 0 := by
      refine (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae ?_ hFint).mp hzero
      filter_upwards with ξ
      positivity
    have hae1 : ∀ᵐ ξ : ℂ, ξ ∈ {ξ : ℂ | ‖ξ‖ < 1} → ‖F ξ‖ ^ 2 = 0 := by
      refine (MeasureTheory.ae_restrict_iff' hBmeas).mp ?_
      filter_upwards [hae0] with ξ h
      exact h
    filter_upwards [hae1] with ξ h hξB _
    have hF0 : F ξ = 0 := by
      have h2 := h hξB
      exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2)
    rw [hF] at hF0
    rw [← hPhi ξ (DZ H ξ)]
    exact sub_eq_zero.mp hF0
  have h18 : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H := by
    refine ⟨a, b, hww, ?_⟩
    filter_upwards [hwa, h5prime] with ξ h1 h2 hξB hξ0
    rw [(h1 hξB).1, (h1 hξB).2]
    exact h2 hξB hξ0
  refine ⟨H, hHW, hHcont, hHcd, h18, ?_, ?_⟩
  · -- the `W^{1,2}` convergence, read for `A` through Step 1
    refine hHtend.congr (fun N => ?_)
    rw [show (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p At k z)
        = (fun z : ℂ => ∑ k ∈ Finset.Icc n (n + N), Thm2Term n p A k z) from
      funext (fun z => hSeq N z)]
    congr 1
    · congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
      simp only [hSeq N]
  · -- ## Step 4: the energy bound, from `EnergyIdentity` at `Ã`
    have hae : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ := hdiffH
    have hqr := Eq18ImpliesQuasiregular p hp n {ξ : ℂ | ‖ξ‖ < 1} H hHW h18
    have hcompEI : ∀ k : ℤ, (n : ℤ) < k →
        At (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (At k) :=
      fun k hk => hAtcomp k (le_of_lt hk)
    have hEIH := (hEI H At hHcont hae h18 hqr hHint hHfour hcompEI).2.2.2.2
    refine le_trans hEIH (le_of_eq ?_)
    congr 1
    refine tsum_congr (fun m => ?_)
    rw [hAteq ((n : ℤ) + 1 + (m : ℤ)) (by omega)]
