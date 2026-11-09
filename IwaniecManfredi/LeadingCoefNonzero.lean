import IwaniecManfredi.SeriesTermwiseDeriv
import IwaniecManfredi.QuasiconformalOn
import IwaniecManfredi.HomeoCircleIndex

/-- The paper's step "Applying argument principle, we find that `A_{n+1} ≠ 0`"
(`paper.tex:382`), together with `A_n = 0`.  The index of the image of a small
circle is computed in two ways: `HomeoCircleIndex` makes it `±1` because `H` is
a homeomorphism fixing the origin, while the leading term of (19) makes it
`m - n`, where `m` is the least index carrying a nonzero coefficient.  The
second computation needs no homotopy: factoring out the model circle of index
`m - n` leaves a loop in the open right half plane, because `|ε_m| < 1` by (24),
and a half-plane loop has index `0` by integrality. -/
theorem LeadingCoefNonzero (n : ℕ) (p : ℝ) (K : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (hK : 1 ≤ K)
    (H : ℂ → ℂ) (A : ℤ → ℂ)
    (hc : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1})
    (hdiff : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ)
    (h18 : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H)
    (hqc : QuasiconformalOn K {ξ : ℂ | ‖ξ‖ < 1} H)
    (hH0 : H 0 = 0)
    (hA : ∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ))
    (hcomp : ∀ k : ℤ, (n : ℤ) ≤ k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k))
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    A (n : ℤ) = 0 ∧ A ((n : ℤ) + 1) ≠ 0 := by
  classical
  obtain ⟨hqr, hinj, -, hHopen, psi, hpsi, hpsic⟩ := hqc
  have hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H := hqr.2.1
  obtain ⟨hSa, hSb, -, -, -⟩ :=
    SeriesTermwiseDeriv n p hn hp H A hc hw hdiff h18 hA hcomp hsum
  obtain ⟨hlamn, hepsn, hepsbd, -⟩ := LambdaEpsEstimates n p hn hp
  have hγn : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have h0B : (0 : ℂ) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by simp
  -- ## Step 0: the exponents
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hLmono : ∀ k k' : ℕ, k < k' → LambdaCoef n k p < LambdaCoef n k' p := by
    intro k k' hk
    have h1 : (k : ℝ) < (k' : ℝ) := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : (k : ℝ) ^ 2 < (k' : ℝ) ^ 2 := by nlinarith only [h1, h0]
    have hrad : 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
        < 4 * (k' : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      nlinarith only [hsq, hp0]
    have hnn : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      have := sq_nonneg (p - 2)
      positivity
    have hs := Real.sqrt_lt_sqrt hnn hrad
    simp only [LambdaCoef]
    linarith only [hs]
  -- `T_k ≡ 0` as soon as `A_k = 0`
  have hT0 : ∀ k : ℕ, A (k : ℤ) = 0 → ∀ ξ : ℂ, Thm2Term n p A k ξ = 0 := by
    intro k hk ξ
    simp [Thm2Term, hk]
  -- `T_n ≡ A_n` off the origin
  have hTn : ∀ ξ : ℂ, ξ ≠ 0 → Thm2Term n p A n ξ = A (n : ℤ) := by
    intro ξ hξ
    have hpn : (ξ : ℂ) ^ n ≠ 0 := pow_ne_zero n hξ
    simp only [Thm2Term, hlamn, hepsn]
    rw [show (0 : ℝ) + (n : ℝ) - (n : ℝ) = 0 from by ring, Real.rpow_zero,
      zpow_neg, zpow_natCast]
    push_cast
    field_simp
    ring
  -- ## Step 1: `A_n = 0`
  have hAn : A (n : ℤ) = 0 := by
    obtain ⟨C, hC0, hCb⟩ := hSb (1 / 2) (by norm_num) (by norm_num) n le_rfl
    have hbd : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ 1 / 2 →
        ‖H ξ - A (n : ℤ)‖ ≤ C * ‖ξ‖ ^ GammaExp n p := by
      intro ξ h1 h2
      have h := hCb ξ h1 h2
      rw [Finset.Icc_self, Finset.sum_singleton, hTn ξ (norm_pos_iff.mp h1)] at h
      simpa only [GammaExp] using h
    have hF : Filter.NeBot (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by infer_instance
    have hev : ∀ᶠ ξ : ℂ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
        ‖H ξ - A (n : ℤ)‖ ≤ C * ‖ξ‖ ^ GammaExp n p := by
      have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ nhds (0 : ℂ) :=
        Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with ξ h1 h2
      refine hbd ξ (norm_pos_iff.mpr h2) ?_
      have := (Metric.mem_ball.mp h1)
      rw [dist_zero_right] at this
      linarith only [this]
    have hten : Filter.Tendsto (fun ξ : ℂ => C * ‖ξ‖ ^ GammaExp n p)
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) := by
      have h1 : ContinuousAt (fun x : ℝ => x ^ GammaExp n p) 0 :=
        Real.continuousAt_rpow_const 0 (GammaExp n p) (Or.inr hγn.le)
      have h2 : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖) (nhds (0 : ℂ)) (nhds 0) := by
        have hcn := (continuous_norm (E := ℂ)).continuousAt (x := (0 : ℂ))
        rw [ContinuousAt, norm_zero] at hcn
        exact hcn
      have h3 : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖ ^ GammaExp n p) (nhds (0 : ℂ)) (nhds 0) := by
        have h4 := h1.tendsto.comp h2
        rw [Real.zero_rpow (ne_of_gt hγn)] at h4
        exact h4
      have h5 : Filter.Tendsto (fun ξ : ℂ => C * ‖ξ‖ ^ GammaExp n p)
          (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (C * 0)) :=
        (h3.const_mul C).mono_left nhdsWithin_le_nhds
      rw [mul_zero] at h5
      exact h5
    have hlim1 : Filter.Tendsto (fun ξ : ℂ => H ξ - A (n : ℤ))
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) := squeeze_zero_norm' hev hten
    have hlim2 : Filter.Tendsto H (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (A (n : ℤ))) := by
      have := hlim1.add_const (A (n : ℤ))
      simpa using this
    have hlim3 : Filter.Tendsto H (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (0 : ℂ)) := by
      have hca : ContinuousAt H 0 := hc.continuousAt (hBopen.mem_nhds h0B)
      have hmo : Filter.Tendsto H (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (H 0)) :=
        hca.tendsto.mono_left nhdsWithin_le_nhds
      rwa [hH0] at hmo
    exact (tendsto_nhds_unique hlim2 hlim3)
  -- ## Step 2: a least nonvanishing index
  have hex : ∃ i : ℕ, A ((n : ℤ) + 1 + (i : ℤ)) ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    simp only [not_not] at hcon
    have hall : ∀ k : ℕ, n ≤ k → A (k : ℤ) = 0 := by
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with h | h
      · rw [← h]; exact hAn
      · obtain ⟨i, hi⟩ : ∃ i : ℕ, k = n + 1 + i := ⟨k - n - 1, by omega⟩
        have hcast : ((k : ℕ) : ℤ) = (n : ℤ) + 1 + (i : ℤ) := by
          rw [hi]; push_cast; ring
        rw [hcast]
        exact hcon i
    have hHz : H ((1 : ℂ) / 2) = 0 := by
      have hnorm : ‖(1 : ℂ) / 2‖ = 1 / 2 := by norm_num
      have h1 : (0 : ℝ) < ‖(1 : ℂ) / 2‖ := by rw [hnorm]; norm_num
      have h2 : ‖(1 : ℂ) / 2‖ < 1 := by rw [hnorm]; norm_num
      have hs := hSa ((1 : ℂ) / 2) h1 h2
      have hz : (fun m : ℕ => Thm2Term n p A (n + m) ((1 : ℂ) / 2)) = fun _ => 0 := by
        funext i
        exact hT0 (n + i) (hall (n + i) (by omega)) _
      rw [hz] at hs
      exact (hasSum_zero.unique hs).symm
    have h12 : ((1 : ℂ) / 2) ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
      simp only [Set.mem_ofPred_eq]
      norm_num
    have := hinj h12 h0B (by rw [hHz, hH0])
    norm_num at this
  obtain ⟨m, hmdef, hmne, hmmin⟩ :
      ∃ m : ℕ, n + 1 ≤ m ∧ A (m : ℤ) ≠ 0 ∧ ∀ k : ℕ, n ≤ k → k < m → A (k : ℤ) = 0 := by
    refine ⟨n + 1 + Nat.find hex, by omega, ?_, ?_⟩
    · have hspec := Nat.find_spec hex
      have hcast : ((n + 1 + Nat.find hex : ℕ) : ℤ)
          = (n : ℤ) + 1 + ((Nat.find hex : ℕ) : ℤ) := by push_cast; ring
      rw [hcast]
      exact hspec
    · intro k hk hklt
      rcases Nat.eq_or_lt_of_le hk with h | h
      · rw [← h]; exact hAn
      · obtain ⟨i, hi⟩ : ∃ i : ℕ, k = n + 1 + i := ⟨k - n - 1, by omega⟩
        have hilt : i < Nat.find hex := by omega
        have hz := Nat.find_min hex hilt
        simp only [not_not] at hz
        have hcast : ((k : ℕ) : ℤ) = (n : ℤ) + 1 + (i : ℤ) := by
          rw [hi]; push_cast; ring
        rw [hcast]
        exact hz
  have hmn : n ≤ m := by omega
  have hAmnorm : (0 : ℝ) < ‖A (m : ℤ)‖ := norm_pos_iff.mpr hmne
  have hsumIcc : ∀ ξ : ℂ, (∑ k ∈ Finset.Icc n m, Thm2Term n p A k ξ) = Thm2Term n p A m ξ := by
    intro ξ
    refine Finset.sum_eq_single_of_mem m (Finset.mem_Icc.mpr ⟨hmn, le_rfl⟩) ?_
    intro b hb hbne
    exact hT0 b (hmmin b (Finset.mem_Icc.mp hb).1
      (lt_of_le_of_ne (Finset.mem_Icc.mp hb).2 hbne)) ξ
  -- ## Step 3: the leading profile
  have hepsm : |EpsCoef n m p| < 1 := hepsbd m hmdef
  have hone : (0 : ℝ) < 1 - |EpsCoef n m p| := by linarith only [hepsm]
  -- ## Step 4: the tail
  obtain ⟨C₁, hC₁0, hC₁b⟩ := hSb (1 / 2) (by norm_num) (by norm_num) m hmn
  -- ## Step 5: `H` does not vanish off the origin, and the index is `±1`
  have hHne : ∀ ξ : ℂ, ‖ξ‖ < 1 → ξ ≠ 0 → H ξ ≠ 0 := by
    intro ξ hξ1 hξ0 hz
    exact hξ0 (hinj hξ1 h0B (by rw [hz, hH0]))
  obtain ⟨ρ₀, hρ₀0, hρ₀⟩ :=
    HomeoCircleIndex {ξ : ℂ | ‖ξ‖ < 1} hBopen h0B H psi hc hinj hHopen hpsi hpsic hH0
  -- ## Step 6: the radius
  have hd0 : 0 < LambdaCoef n (m + 1) p - LambdaCoef n m p := by
    have := hLmono m (m + 1) (by omega)
    linarith only [this]
  obtain ⟨Bq, hBqdef⟩ : ∃ Bq : ℝ,
      Bq = (1 - |EpsCoef n m p|) * ‖A (m : ℤ)‖ / (2 * C₁ + 1) := ⟨_, rfl⟩
  have hBq0 : 0 < Bq := by
    rw [hBqdef]
    have : (0 : ℝ) < 2 * C₁ + 1 := by linarith only [hC₁0]
    positivity
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min (min ρ₀ (1 / 2))
      (Bq ^ (1 / (LambdaCoef n (m + 1) p - LambdaCoef n m p))) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min hρ₀0 (by norm_num)) (Real.rpow_pos_of_pos hBq0 _)
  have hrρ₀ : r ≤ ρ₀ := by rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hr1 : r < 1 := by linarith only [hrhalf]
  have hrd : C₁ * r ^ (LambdaCoef n (m + 1) p - LambdaCoef n m p)
      < (1 - |EpsCoef n m p|) * ‖A (m : ℤ)‖ := by
    have hstep : r ^ (LambdaCoef n (m + 1) p - LambdaCoef n m p) ≤ Bq := by
      have h1 : r ≤ Bq ^ (1 / (LambdaCoef n (m + 1) p - LambdaCoef n m p)) := by
        rw [hrdef]; exact min_le_right _ _
      have h2 := Real.rpow_le_rpow hr0.le h1 hd0.le
      refine le_trans h2 (le_of_eq ?_)
      rw [← Real.rpow_mul hBq0.le, one_div_mul_cancel (ne_of_gt hd0), Real.rpow_one]
    have hq : (0 : ℝ) < 2 * C₁ + 1 := by linarith only [hC₁0]
    have h3 : C₁ * r ^ (LambdaCoef n (m + 1) p - LambdaCoef n m p) ≤ C₁ * Bq :=
      mul_le_mul_of_nonneg_left hstep hC₁0
    have h4 : C₁ * Bq < (1 - |EpsCoef n m p|) * ‖A (m : ℤ)‖ := by
      rw [hBqdef, mul_div_assoc']
      rw [div_lt_iff₀ hq]
      have hX : (0 : ℝ) < (1 - |EpsCoef n m p|) * ‖A (m : ℤ)‖ := mul_pos hone hAmnorm
      linarith only [hX, mul_nonneg hC₁0 hX.le]
    linarith only [h3, h4]
  -- the circle, in the three coercion shapes that the dependencies ask for
  have hexpnorm : ∀ x : ℝ, ‖Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)‖ = 1 := by
    intro x
    have he : (2 : ℂ) * (Real.pi : ℂ) * ((x : ℝ) : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hexpnorm2 : ∀ x y : ℝ,
      ‖Complex.exp (2 * Real.pi * (x : ℝ) * (y : ℝ) * Complex.I)‖ = 1 := by
    intro x y
    have he : (2 : ℂ) * (Real.pi : ℂ) * ((x : ℝ) : ℂ) * ((y : ℝ) : ℂ)
        = ((2 * Real.pi * x * y : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hexp0 : Complex.exp (2 * (Real.pi : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [he, Complex.exp_zero]
  have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I
        = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_two_pi_mul_I]
  have hexp0k : ∀ k : ℤ, Complex.exp
      (2 * (Real.pi : ℂ) * (((k : ℝ)) : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I) = 1 := by
    intro k
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((k : ℝ)) : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I
        = 0 := by push_cast; ring
    rw [he, Complex.exp_zero]
  have hexp1k : ∀ k : ℤ, Complex.exp
      (2 * (Real.pi : ℂ) * (((k : ℝ)) : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I) = 1 := by
    intro k
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((k : ℝ)) : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
  have hcnorm : ∀ x : ℝ,
      ‖(r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)‖ = r := by
    intro x
    rw [norm_mul, hexpnorm x, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hcB : ∀ x : ℝ, ((r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I))
      ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro x
    simp only [Set.mem_ofPred_eq, hcnorm x]
    exact hr1
  have hcne : ∀ x : ℝ, ((r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)) ≠ 0 := by
    intro x hcon
    have h := hcnorm x
    rw [hcon, norm_zero] at h
    exact absurd h.symm (ne_of_gt hr0)
  -- the three loops
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ,
      w = A (m : ℤ) * ((r ^ LambdaCoef n m p : ℝ) : ℂ) := ⟨_, rfl⟩
  have hwnorm : ‖w‖ = ‖A (m : ℤ)‖ * r ^ LambdaCoef n m p := by
    rw [hwdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hr0 _)]
  have hwne : w ≠ 0 := by
    rw [← norm_ne_zero_iff, hwnorm]
    have := Real.rpow_pos_of_pos hr0 (LambdaCoef n m p)
    positivity
  obtain ⟨γ, hγapp⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval,
      f t = H ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I)) :=
    ⟨⟨fun t => H ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I)),
      hc.comp_continuous (by fun_prop) (fun t => hcB (t : ℝ))⟩, fun _ => rfl⟩
  obtain ⟨α, hαapp⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval,
      f t = w * Complex.exp
        (2 * Real.pi * ((((m : ℤ) - (n : ℤ)) : ℤ) : ℝ) * (t : ℝ) * Complex.I) :=
    ⟨⟨fun t => w * Complex.exp
        (2 * Real.pi * ((((m : ℤ) - (n : ℤ)) : ℤ) : ℝ) * (t : ℝ) * Complex.I),
      by fun_prop⟩, fun _ => rfl⟩
  have hγne : ∀ t, γ t ≠ 0 := by
    intro t
    rw [hγapp t]
    exact hHne _ (hcB (t : ℝ)) (hcne (t : ℝ))
  have hαne : ∀ t, α t ≠ 0 := by
    intro t
    rw [hαapp t]
    exact mul_ne_zero hwne (Complex.exp_ne_zero _)
  obtain ⟨β, hβapp⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval, f t = γ t / α t :=
    ⟨⟨fun t => γ t / α t, γ.continuous.div α.continuous hαne⟩, fun _ => rfl⟩
  have hβne : ∀ t, β t ≠ 0 := by
    intro t
    rw [hβapp t]
    exact div_ne_zero (hγne t) (hαne t)
  have hmul : ∀ t, γ t = α t * β t := by
    intro t
    rw [hβapp t, mul_div_cancel₀ _ (hαne t)]
  obtain ⟨hWCa, hWCb, hWCc, hWCd⟩ := WindingCalculus
  obtain ⟨u, hudef⟩ : ∃ u : ℂ, u = starRingEnd ℂ (A (m : ℤ)) / A (m : ℤ) := ⟨_, rfl⟩
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_conj, div_self (ne_of_gt hAmnorm)]
  -- the leading term, factored as the model circle times a loop near `1`
  have hTmval : ∀ t : ↑unitInterval,
      Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I)) = α t * (1 + ((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I)) := by
    intro t
    have hth := (Thm2TermSolvesEq18 n p hn hp m hmn A).2.1 r hr0 (2 * Real.pi * (t : ℝ))
    have hbridge : ((r : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I))
        = (r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I) := by
      congr 2
      push_cast; ring
    rw [hbridge] at hth
    have e1 : Complex.exp ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℂ) * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * (Real.pi : ℂ) * ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast; ring
    have e2 : Complex.exp (((-(m : ℤ) - (n : ℤ) : ℤ) : ℂ)
          * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * (Real.pi : ℂ) * ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) * Complex.I)
          * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [hth, hαapp t, hwdef, e1, e2, hudef]
    field_simp
  -- the pointwise lower bound on `Re β`
  have hReβ : ∀ t : ↑unitInterval, 0 < (β t).re := by
    intro t
    have hξn : ‖((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))‖ = r := hcnorm (t : ℝ)
    have htail := hC₁b ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I)) (by rw [hξn]; exact hr0) (by rw [hξn]; exact hrhalf)
    rw [hsumIcc, hξn, ← hγapp t] at htail
    have hEtn : ‖Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I)‖ = 1 := hexpnorm2 (-(2 * (m : ℝ))) ((t : ℝ))
    have hαn : ‖α t‖ = ‖A (m : ℤ)‖ * r ^ LambdaCoef n m p := by
      rw [hαapp t, norm_mul, hexpnorm2 ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℝ)) ((t : ℝ)), mul_one, hwnorm]
    have hβdec : β t = (1 + ((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I))
        + (γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t := by
      have hαt : α t ≠ 0 := hαne t
      rw [hβapp t, hTmval t]
      field_simp
      ring
    have hA1 : 1 - |EpsCoef n m p| ≤ (1 + ((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I)).re := by
      have hz : ‖((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I)‖ = |EpsCoef n m p| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hunorm, hEtn]
        ring
      have h1 := Complex.abs_re_le_norm (((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I))
      have h2 := neg_abs_le ((((EpsCoef n m p : ℝ) : ℂ) * u * Complex.exp (2 * Real.pi * ((-(2 * (m : ℝ))) : ℝ) * ((t : ℝ)) * Complex.I)).re)
      rw [hz] at h1
      rw [Complex.add_re, Complex.one_re]
      linarith only [h1, h2]
    have hA2 : -‖(γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t‖
        ≤ ((γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t).re := by
      have h1 := Complex.abs_re_le_norm ((γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t)
      have h2 := neg_abs_le (((γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t).re)
      linarith only [h1, h2]
    have hsplit : r ^ LambdaCoef n (m + 1) p
        = r ^ LambdaCoef n m p * r ^ (LambdaCoef n (m + 1) p - LambdaCoef n m p) := by
      rw [← Real.rpow_add hr0]
      congr 1
      ring
    have hpos : (0 : ℝ) < r ^ LambdaCoef n m p := Real.rpow_pos_of_pos hr0 _
    have hA3 : ‖(γ t - Thm2Term n p A m ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) / α t‖ < 1 - |EpsCoef n m p| := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr (hαne t)), hαn]
      rw [hsplit] at htail
      have hkey := mul_lt_mul_of_pos_right hrd hpos
      linarith only [htail, hkey]
    rw [hβdec, Complex.add_re]
    linarith only [hA1, hA2, hA3]
  -- ## Step 7: `ind β = 0`
  obtain ⟨Θ, hΘ0, hΘang, hΘpol⟩ := hWCa β hβne
  have hβnorm : ∀ t : ↑unitInterval, 0 < ‖β t‖ := fun t => norm_pos_iff.mpr (hβne t)
  have hcos : ∀ t : ↑unitInterval, 0 < Real.cos (Θ t) := by
    intro t
    have hre : (β t).re = ‖β t‖ * Real.cos (Θ t) := by
      conv_lhs => rw [hΘpol t]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have h := hReβ t
    rw [hre] at h
    rcases le_or_gt (Real.cos (Θ t)) 0 with hcc | hcc
    · exfalso
      nlinarith only [h, hβnorm t, hcc]
    · exact hcc
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hargle := Complex.arg_le_pi (β 0)
  have hargge := Complex.neg_pi_lt_arg (β 0)
  have hΘ0lt : Θ (0 : ↑unitInterval) < Real.pi / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : Θ (0 : ↑unitInterval) ≤ Real.pi + Real.pi / 2 := by
      linarith only [hargle, hΘ0, hπ]
    have h3 := Real.cos_nonpos_of_pi_div_two_le_of_le hcon h2
    linarith only [h3, hcos 0]
  have hΘ0gt : -(Real.pi / 2) < Θ (0 : ↑unitInterval) := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : Real.pi / 2 ≤ -(Θ (0 : ↑unitInterval)) := by linarith only [hcon]
    have h2 : -(Θ (0 : ↑unitInterval)) ≤ Real.pi + Real.pi / 2 := by
      linarith only [hargge, hΘ0, hπ]
    have h3 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
    rw [Real.cos_neg] at h3
    linarith only [h3, hcos 0]
  have hprec : IsPreconnected (Set.univ : Set ↑unitInterval) := isPreconnected_univ
  have hup : ∀ t : ↑unitInterval, Θ t < Real.pi / 2 := by
    intro t
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨s, -, hs⟩ := hprec.intermediate_value (Set.mem_univ (0 : ↑unitInterval))
      (Set.mem_univ t) Θ.continuous.continuousOn ⟨le_of_lt hΘ0lt, hcon⟩
    have h := hcos s
    rw [hs, Real.cos_pi_div_two] at h
    exact absurd h (lt_irrefl 0)
  have hlow : ∀ t : ↑unitInterval, -(Real.pi / 2) < Θ t := by
    intro t
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨s, -, hs⟩ := hprec.intermediate_value (Set.mem_univ t)
      (Set.mem_univ (0 : ↑unitInterval)) Θ.continuous.continuousOn
      ⟨hcon, le_of_lt hΘ0gt⟩
    have h := hcos s
    rw [hs, Real.cos_neg, Real.cos_pi_div_two] at h
    exact absurd h (lt_irrefl 0)
  have hγloop : γ 0 = γ 1 := by
    rw [hγapp 0, hγapp 1, Set.Icc.coe_zero, Set.Icc.coe_one, hexp0, hexp1]
  have hαloop : α 0 = α 1 := by
    rw [hαapp 0, hαapp 1, Set.Icc.coe_zero, Set.Icc.coe_one,
      hexp0k ((((m : ℤ) - (n : ℤ)) : ℤ)), hexp1k ((((m : ℤ) - (n : ℤ)) : ℤ))]
  have hβloop : β 0 = β 1 := by rw [hβapp 0, hβapp 1, hγloop, hαloop]
  obtain ⟨e, he⟩ := hWCc β hβne hβloop
  have hbb := hWCb β hβne Θ hΘ0 hΘang
  rw [he] at hbb
  have he0 : e = 0 := by
    have h1 := hup 1
    have h2 := hlow 1
    have h3 := hup 0
    have h4 := hlow 0
    have hlt : (e : ℝ) < 1 := by
      by_contra hcc
      rw [not_lt] at hcc
      nlinarith only [hbb, hπ, h1, h4, hcc,
        mul_nonneg hπ.le (by linarith only [hcc] : (0 : ℝ) ≤ (e : ℝ) - 1)]
    have hgt : (-1 : ℝ) < (e : ℝ) := by
      by_contra hcc
      rw [not_lt] at hcc
      nlinarith only [hbb, hπ, h2, h3, hcc,
        mul_nonneg hπ.le (by linarith only [hcc] : (0 : ℝ) ≤ -1 - (e : ℝ))]
    have hlt' : e < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < e := by exact_mod_cast hgt
    omega
  -- ## Step 8: conclusion
  have hαind : WindingNumber α hαne = ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℤ) : ℝ) :=
    hWCd w ((((m : ℤ) - (n : ℤ)) : ℤ)) α hαne hwne hαapp
  have h11 : WindingNumber γ hγne = WindingNumber α hαne + WindingNumber β hβne :=
    WindingAdditivity.1 α β γ hαne hβne hγne hmul
  rw [hαind, he, he0] at h11
  have hind := hρ₀ r hr0 hrρ₀ γ hγapp hγne
  have hmn1 : (m : ℤ) - (n : ℤ) = 1 := by
    rcases hind with h | h
    · rw [h] at h11
      have hc1 : ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℤ) : ℝ) = (1 : ℝ) := by
        push_cast at h11 ⊢
        linarith only [h11]
      exact_mod_cast hc1
    · rw [h] at h11
      have hc1 : ((((((m : ℤ) - (n : ℤ)) : ℤ)) : ℤ) : ℝ) = (-1 : ℝ) := by
        push_cast at h11 ⊢
        linarith only [h11]
      have hneg : (m : ℤ) - (n : ℤ) = -1 := by exact_mod_cast hc1
      omega
  refine ⟨hAn, ?_⟩
  have hmeq : ((n : ℤ) + 1) = (m : ℤ) := by omega
  rw [hmeq]
  exact hmne
