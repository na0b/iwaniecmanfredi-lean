import IwaniecManfredi.Eq18Rescale
import IwaniecManfredi.Thm2Expansion
import IwaniecManfredi.SeriesTermwiseDeriv
import IwaniecManfredi.LeadingCoefNonzero
import IwaniecManfredi.QCDistortionPolar
import IwaniecManfredi.Jac

/-- Corollary 1 of the paper: the smoothness of `H` off the origin and the
estimates (41), (42) and (43), for a local solution of (18) quasiconformal near
the origin with `H(0) = 0`, together with the closed form (44) of `γ_n`.  The
printed corollary (`paper.tex:360-374`) assumes no smoothness, while (43)
bounds the derivatives of every order, so smoothness off the origin is a
*conclusion* here: it is produced by term-by-term differentiation of the
expansion (19), the paper's own step at `paper.tex:387-388`, and carried back
through the rescaling.  All three estimates share one radius `ρ` and
one pair of constants `c < C`, as the paper states them; splitting them across
separate radii would be a strictly weaker statement.  The hypothesis is local,
so the proof begins with the rescaling of `Eq18Rescale`, and the derivative
bounds are transported back by its scaling clause. -/
theorem Cor1 (n : ℕ) (p : ℝ) (K : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (hK : 1 ≤ K)
    (V : Set ℂ) (hV : IsOpen V) (h0 : (0 : ℂ) ∈ V) (H : ℂ → ℂ)
    (hcont : ContinuousOn H V)
    (hdiff : ∀ᵐ ξ : ℂ, ξ ∈ V → DifferentiableAt ℝ H ξ)
    (hqc : QuasiconformalOn K V H)
    (h18 : SolvesEq18 n p V H)
    (hH0 : H 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ Cm : ℕ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball (0 : ℂ) ρ \ {0}) ∧
      (∀ ξ : ℂ, ‖ξ‖ ≤ ρ →
        c * ‖ξ‖ ^ GammaExp n p ≤ ‖H ξ‖ ∧ ‖H ξ‖ ≤ C * ‖ξ‖ ^ GammaExp n p) ∧
      (∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ ρ →
        c * ‖ξ‖ ^ (2 * GammaExp n p - 2) ≤ Jac H ξ ∧
          Jac H ξ ≤ C * ‖ξ‖ ^ (2 * GammaExp n p - 2)) ∧
      (∀ (m : ℕ) (ξ : ℂ), 0 < ‖ξ‖ → ‖ξ‖ ≤ ρ →
        ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
          ≤ Cm m * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))) ∧
      GammaExp n p
        = (n : ℝ) / 2
            * (-p + Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnne : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  -- ## Step 0: monotonicity of the exponents, and (44)
  have hLmono : ∀ k k' : ℕ, k < k' → LambdaCoef n k p < LambdaCoef n k' p := by
    intro k k' hk
    have h1 : (k : ℝ) < (k' : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : (k : ℝ) ^ 2 < (k' : ℝ) ^ 2 := by nlinarith only [h1, hk0]
    have hrad : 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
        < 4 * (k' : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      nlinarith only [hsq, hp0]
    have hnn : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
      have := sq_nonneg (p - 2)
      positivity
    have hs := Real.sqrt_lt_sqrt hnn hrad
    simp only [LambdaCoef]
    linarith only [hs]
  have h44 : GammaExp n p
      = (n : ℝ) / 2
          * (-p + Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)) := by
    have hX : (0 : ℝ) ≤ 4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2 := by
      have := sq_nonneg (p - 2)
      positivity
    have hrw : (n : ℝ) * Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2)
        = Real.sqrt (4 * ((n : ℝ) + 1) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) := by
      have h1 : Real.sqrt ((n : ℝ) ^ 2
            * (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2))
          = Real.sqrt ((n : ℝ) ^ 2)
            * Real.sqrt (4 * (1 + 1 / (n : ℝ)) ^ 2 * (p - 1) + (p - 2) ^ 2) :=
        Real.sqrt_mul (by positivity) _
      rw [Real.sqrt_sq hn0.le] at h1
      rw [← h1]
      congr 1
      field_simp
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    simp only [GammaExp, LambdaCoef, hcast]
    linarith only [hrw]
  -- ## Step 1: rescaling
  obtain ⟨ε, hε0, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = ε / 2 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; positivity
  have hthalf : t < ε := by rw [htdef]; linarith
  have hballV : Metric.closedBall (0 : ℂ) t ⊆ V := by
    intro z hz
    refine hεV ?_
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith only [hz, hthalf]
  obtain ⟨hGa, hGb, hGc, hGd, hGe, hGf, hGg⟩ :=
    Eq18Rescale n p K t hp hK ht V hV hballV H hcont hdiff hqc h18
  have hG0 : (fun ζ : ℂ => H ((t : ℂ) * ζ)) 0 = 0 := by
    show H ((t : ℂ) * 0) = 0
    rw [mul_zero, hH0]
  -- ## Step 2: the coefficients
  obtain ⟨CT, -, hTE⟩ := Thm2Expansion n p hn hp
  obtain ⟨A, hAcomp, hAfour, hAsum, -, -⟩ :=
    hTE (fun ζ : ℂ => H ((t : ℂ) * ζ)) hGd hGa hGb hGc hGe
  obtain ⟨Fs, hFs⟩ : ∃ F : ℕ → ℝ, ∀ m : ℕ,
      F m = ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hshift : Summable (fun m : ℕ => Fs (m + 1)) := by
    refine hAsum.congr (fun m => ?_)
    have hz : (n : ℤ) + 1 + (m : ℤ) = (n : ℤ) + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hFs, hz]
    push_cast
    ring
  have h6 : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2) :=
    ((summable_nat_add_iff 1).mp hshift).congr (fun m => hFs m)
  -- ## Step 3: `A_n = 0` and `A_{n+1} ≠ 0`
  obtain ⟨hAn, hAn1⟩ := LeadingCoefNonzero n p K hn hp hK
    (fun ζ : ℂ => H ((t : ℂ) * ζ)) A hGa hGb hGc hGf hG0 hAfour hAcomp h6
  -- ## Step 4: the leading profile constants
  obtain ⟨-, -, hepsbd, -⟩ := LambdaEpsEstimates n p hn hp
  have hepsn1 : |EpsCoef n (n + 1) p| < 1 := hepsbd (n + 1) le_rfl
  obtain ⟨a, hadef⟩ : ∃ a : ℝ,
      a = ‖A ((n : ℤ) + 1)‖ * (1 - |EpsCoef n (n + 1) p|) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [hadef]
    have h1 : (0 : ℝ) < ‖A ((n : ℤ) + 1)‖ := norm_pos_iff.mpr hAn1
    have h2 : (0 : ℝ) < 1 - |EpsCoef n (n + 1) p| := by linarith only [hepsn1]
    positivity
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = GammaExp n p * a / 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hbdef]; positivity
  -- ## Step 5: the series estimates for `G`
  obtain ⟨hSa, hSb, hSc, hSd, hSe⟩ :=
    SeriesTermwiseDeriv n p hn hp (fun ζ : ℂ => H ((t : ℂ) * ζ)) A hGa hGd hGb hGc
      hAfour hAcomp h6
  -- (11'): the smoothness of `H` off the origin, and the derivative dictionary
  obtain ⟨hHsm, hdict⟩ := hGg hSe
  -- the exponent gap
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = LambdaCoef n (n + 2) p - GammaExp n p := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    have h := hLmono (n + 1) (n + 2) (by omega)
    rw [hddef]
    simp only [GammaExp]
    linarith only [h]
  -- the family (15) of (d'), and the two constants it supplies
  have hSdm : ∀ m : ℕ, ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ 1 / 2 →
      ∑ v : Fin m → Fin 2,
          ‖PartialWord (List.ofFn v) (fun z : ℂ => H ((t : ℂ) * z)) ξ‖
        ≤ Cm * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) :=
    fun m => hSd hAn m (1 / 2) (by norm_num) (by norm_num)
  choose Cp hCp0 hCpb using hSdm
  -- (b') and (c') at `j = n + 1`
  obtain ⟨C3, hC30, hC3b⟩ := hSb (1 / 2) (by norm_num) (by norm_num) (n + 1) (by omega)
  obtain ⟨C4, hC40, hC4b⟩ := hSc (1 / 2) (by norm_num) (by norm_num) (n + 1) (by omega)
  -- the radii (13) and (17)
  obtain ⟨ρ1, hρ1def⟩ : ∃ r : ℝ,
      r = min (1 / 2) ((a / (2 * (C3 + 1))) ^ (1 / d)) := ⟨_, rfl⟩
  have hq3 : (0 : ℝ) < 2 * (C3 + 1) := by linarith only [hC30]
  have hρ10 : 0 < ρ1 := by
    rw [hρ1def]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hρ1half : ρ1 ≤ 1 / 2 := by rw [hρ1def]; exact min_le_left _ _
  obtain ⟨ρ2, hρ2def⟩ : ∃ r : ℝ,
      r = min ρ1 ((b / (C4 + 1)) ^ (1 / d)) := ⟨_, rfl⟩
  have hq4 : (0 : ℝ) < C4 + 1 := by linarith only [hC40]
  have hρ20 : 0 < ρ2 := by
    rw [hρ2def]
    exact lt_min hρ10 (Real.rpow_pos_of_pos (by positivity) _)
  have hρ21 : ρ2 ≤ ρ1 := by rw [hρ2def]; exact min_le_left _ _
  have hρ2half : ρ2 ≤ 1 / 2 := le_trans hρ21 hρ1half
  -- the two constant estimates (13) and (17)
  have hrpowle : ∀ (x y : ℝ), 0 < x → 0 < y → x ≤ y ^ (1 / d) → x ^ d ≤ y := by
    intro x y hx hy hxy
    refine le_trans (Real.rpow_le_rpow hx.le hxy hd0.le) (le_of_eq ?_)
    rw [← Real.rpow_mul hy.le, one_div_mul_cancel (ne_of_gt hd0), Real.rpow_one]
  have h13 : C3 * ρ2 ^ d ≤ a / 2 := by
    have hle : ρ2 ≤ (a / (2 * (C3 + 1))) ^ (1 / d) :=
      le_trans hρ21 (by rw [hρ1def]; exact min_le_right _ _)
    have hstep := hrpowle ρ2 (a / (2 * (C3 + 1))) hρ20 (by positivity) hle
    have hfin : C3 * (a / (2 * (C3 + 1))) ≤ a / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hq3 (by norm_num : (0:ℝ) < 2)]
      nlinarith only [hC30, ha0]
    calc C3 * ρ2 ^ d ≤ C3 * (a / (2 * (C3 + 1))) := mul_le_mul_of_nonneg_left hstep hC30
      _ ≤ a / 2 := hfin
  have h17 : C4 * ρ2 ^ d ≤ b := by
    have hle : ρ2 ≤ (b / (C4 + 1)) ^ (1 / d) := by rw [hρ2def]; exact min_le_right _ _
    have hstep := hrpowle ρ2 (b / (C4 + 1)) hρ20 (by positivity) hle
    have hfin : C4 * (b / (C4 + 1)) ≤ b := by
      rw [mul_div_assoc', div_le_iff₀ hq4]
      nlinarith only [hC40, hb0]
    calc C4 * ρ2 ^ d ≤ C4 * (b / (C4 + 1)) := mul_le_mul_of_nonneg_left hstep hC40
      _ ≤ b := hfin
  -- ## Step 7: the constants
  have htpow : ∀ e : ℝ, (0 : ℝ) < t ^ e := fun e => Real.rpow_pos_of_pos ht e
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = min (a / 2 * t ^ (-GammaExp n p))
      (K⁻¹ * b ^ 2 * t ^ (-(2 * GammaExp n p))) := ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < K := by linarith only [hK]
  have hc0 : 0 < c := by
    rw [hcdef]
    refine lt_min ?_ ?_
    · have := htpow (-GammaExp n p)
      positivity
    · have := htpow (-(2 * GammaExp n p))
      have : (0 : ℝ) < K⁻¹ := inv_pos.mpr hK0
      positivity
  obtain ⟨Cc, hCcdef⟩ : ∃ x : ℝ, x = max (max (Cp 0 * t ^ (-GammaExp n p))
      ((Cp 1) ^ 2 / 4 * t ^ (-(2 * GammaExp n p)))) (c + 1) := ⟨_, rfl⟩
  have hcC : c < Cc := by
    rw [hCcdef]
    exact lt_of_lt_of_le (by linarith only [] : c < c + 1) (le_max_right _ _)
  obtain ⟨Cmf, hCmfdef⟩ : ∃ f : ℕ → ℝ, ∀ m : ℕ,
      f m = Cp m * t ^ (-GammaExp n p) := ⟨_, fun _ => rfl⟩
  -- the smoothness conclusion
  have hsub : Metric.ball (0 : ℂ) (t * ρ2) \ {0} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} := by
    intro z hz
    refine ⟨norm_pos_iff.mpr (by simpa using hz.2), ?_⟩
    have h1 : ‖z‖ < t * ρ2 := by
      have := hz.1
      simpa [Metric.mem_ball, dist_zero_right] using this
    nlinarith only [h1, ht, hρ2half, hρ20]
  have htcne : (t : ℂ) ≠ 0 := by simpa using ne_of_gt ht
  -- ## Step 6: the change of variable `ζ = ξ / t`
  have hscale : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ t * ρ2 →
      ξ = (t : ℂ) * (((t : ℝ) : ℂ)⁻¹ * ξ) ∧
        ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ = ‖ξ‖ / t ∧
        0 < ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ∧ ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ < 1 ∧
        ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ≤ 1 / 2 := by
    intro ξ hξ0 hξρ
    have hζn : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ = ‖ξ‖ / t := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        div_eq_inv_mul]
    have hmul := mul_le_mul_of_nonneg_left hρ2half ht.le
    refine ⟨?_, hζn, ?_, ?_, ?_⟩
    · rw [← mul_assoc, mul_inv_cancel₀ htcne, one_mul]
    · rw [hζn]; positivity
    · rw [hζn, div_lt_one ht]
      nlinarith only [hξρ, hmul, ht, hρ20]
    · rw [hζn, div_le_iff₀ ht]
      linarith only [hξρ, hmul]
  have htm : ∀ m : ℕ, (t ^ (m : ℕ))⁻¹ = t ^ (-(m : ℝ)) := by
    intro m
    rw [Real.rpow_neg ht.le, Real.rpow_natCast]
  -- ## (43)
  have h43 : ∀ (m : ℕ) (ξ : ℂ), 0 < ‖ξ‖ → ‖ξ‖ ≤ t * ρ2 →
      ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        ≤ Cmf m * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
    intro m ξ hξ0 hξρ
    obtain ⟨hxi, hζn, hζ0, hζ1, hζhalf⟩ := hscale ξ hξ0 hξρ
    have hsumeq : ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        = (t ^ (m : ℕ))⁻¹ * ∑ v : Fin m → Fin 2,
            ‖PartialWord (List.ofFn v) (fun z : ℂ => H ((t : ℂ) * z))
              (((t : ℝ) : ℂ)⁻¹ * ξ)‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hw := hdict (List.ofFn v) (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζ1
      rw [← hxi] at hw
      rw [hw, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, List.length_ofFn, ← inv_pow]
    have hS := hCpb m (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζhalf
    have hpow : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ^ (GammaExp n p - (m : ℝ))
        = t ^ (-(GammaExp n p - (m : ℝ))) * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
      rw [hζn, Real.div_rpow (norm_nonneg ξ) ht.le, Real.rpow_neg ht.le]
      ring
    have hcomb : t ^ (-(m : ℝ)) * t ^ (-(GammaExp n p - (m : ℝ)))
        = t ^ (-GammaExp n p) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hfac : (t ^ (m : ℕ))⁻¹
          * (Cp m * ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ^ (GammaExp n p - (m : ℝ)))
        = Cp m * t ^ (-GammaExp n p) * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
      rw [hpow, htm m]
      linear_combination (Cp m * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))) * hcomb
    rw [hsumeq, hCmfdef m]
    calc (t ^ (m : ℕ))⁻¹ * ∑ v : Fin m → Fin 2,
            ‖PartialWord (List.ofFn v) (fun z : ℂ => H ((t : ℂ) * z))
              (((t : ℝ) : ℂ)⁻¹ * ξ)‖
        ≤ (t ^ (m : ℕ))⁻¹
            * (Cp m * ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ^ (GammaExp n p - (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = Cp m * t ^ (-GammaExp n p) * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := hfac
  have hpowe : ∀ (ξ : ℂ) (e : ℝ), ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ^ e = t ^ (-e) * ‖ξ‖ ^ e := by
    intro ξ e
    have hζn : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ = ‖ξ‖ / t := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        div_eq_inv_mul]
    rw [hζn, Real.div_rpow (norm_nonneg ξ) ht.le, Real.rpow_neg ht.le]
    ring
  -- (8): `A_n = 0` kills the `k = n` summand
  have hT0 : ∀ ζ : ℂ, Thm2Term n p A n ζ = 0 := by
    intro ζ
    simp [Thm2Term, hAn]
  have hIcc : ∀ ζ : ℂ, (∑ k ∈ Finset.Icc n (n + 1), Thm2Term n p A k ζ)
      = Thm2Term n p A (n + 1) ζ := by
    intro ζ
    rw [Finset.sum_Icc_succ_top (by omega : n ≤ n + 1), Finset.Icc_self,
      Finset.sum_singleton, hT0 ζ, zero_add]
  -- (10): the lower bound on the leading profile
  have hexpn : ∀ (k : ℤ) (θ : ℝ),
      ‖Complex.exp (((k : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    intro k θ
    have he : ((k : ℤ) : ℂ) * (θ : ℂ) * Complex.I
        = (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hAcast : A (((n + 1 : ℕ)) : ℤ) = A ((n : ℤ) + 1) := by
    congr 1
  have hrev : ∀ x y : ℂ, ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
    intro x y
    have h := norm_add_le (x + y) (-y)
    simp only [add_neg_cancel_right, norm_neg] at h
    linarith only [h]
  have h10 : ∀ ζ : ℂ, ζ ≠ 0 →
      a * ‖ζ‖ ^ GammaExp n p ≤ ‖Thm2Term n p A (n + 1) ζ‖ := by
    intro ζ hζ
    have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hpolar : ζ = ((‖ζ‖ : ℝ) : ℂ)
        * Complex.exp ((Complex.arg ζ : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I ζ).symm
    have hval := (Thm2TermSolvesEq18 n p hn hp (n + 1) (by omega) A).2.1
      ‖ζ‖ hr (Complex.arg ζ)
    rw [← hpolar] at hval
    obtain ⟨X, hX⟩ : ∃ x : ℂ, x = A (((n + 1 : ℕ)) : ℤ)
        * Complex.exp (((((n + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ)
          * ((Complex.arg ζ : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ y : ℂ, y = ((EpsCoef n (n + 1) p : ℝ) : ℂ)
        * starRingEnd ℂ (A (((n + 1 : ℕ)) : ℤ))
        * Complex.exp (((-(((n + 1 : ℕ)) : ℤ) - (n : ℤ) : ℤ) : ℂ)
          * ((Complex.arg ζ : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    have hn1 : ‖X‖ = ‖A ((n : ℤ) + 1)‖ := by
      rw [hX, norm_mul, hexpn _ _, mul_one, hAcast]
    have hn2 : ‖Y‖ = |EpsCoef n (n + 1) p| * ‖A ((n : ℤ) + 1)‖ := by
      rw [hY, norm_mul, norm_mul, hexpn _ _, mul_one, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, hAcast]
    have hprof : a ≤ ‖X + Y‖ := by
      have h := hrev X Y
      rw [hn1, hn2] at h
      rw [hadef]
      linarith only [h]
    rw [hval, ← hX, ← hY, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hr _)]
    have hlam : LambdaCoef n (n + 1) p = GammaExp n p := rfl
    rw [hlam]
    have hpos : (0 : ℝ) < ‖ζ‖ ^ GammaExp n p := Real.rpow_pos_of_pos hr _
    nlinarith only [hprof, hpos]
  -- (14): the lower bound on `G`
  have hGlow : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ ρ2 →
      a / 2 * ‖ζ‖ ^ GammaExp n p ≤ ‖H ((t : ℂ) * ζ)‖ := by
    intro ζ hζ0 hζρ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hζhalf : ‖ζ‖ ≤ 1 / 2 := le_trans hζρ hρ2half
    have htail := hC3b ζ hζ0 hζhalf
    rw [hIcc ζ, show n + 1 + 1 = n + 2 from rfl] at htail
    have hsplit : ‖ζ‖ ^ LambdaCoef n (n + 2) p
        = ‖ζ‖ ^ GammaExp n p * ‖ζ‖ ^ d := by
      rw [← Real.rpow_add hζ0, hddef]
      congr 1
      ring
    have hmono : ‖ζ‖ ^ d ≤ ρ2 ^ d := Real.rpow_le_rpow hζ0.le hζρ hd0.le
    have hpos : (0 : ℝ) < ‖ζ‖ ^ GammaExp n p := Real.rpow_pos_of_pos hζ0 _
    have hlow := h10 ζ hζne
    have hrev2 : ‖Thm2Term n p A (n + 1) ζ‖ - ‖H ((t : ℂ) * ζ) - Thm2Term n p A (n + 1) ζ‖
        ≤ ‖H ((t : ℂ) * ζ)‖ := by
      have h0 := norm_add_le (H ((t : ℂ) * ζ))
        (Thm2Term n p A (n + 1) ζ - H ((t : ℂ) * ζ))
      have h : ‖Thm2Term n p A (n + 1) ζ‖
          ≤ ‖H ((t : ℂ) * ζ)‖
            + ‖Thm2Term n p A (n + 1) ζ - H ((t : ℂ) * ζ)‖ := by simpa using h0
      rw [norm_sub_rev] at h
      linarith only [h]
    have hC3pos : 0 ≤ C3 * ‖ζ‖ ^ d := by positivity
    have hkey : C3 * ‖ζ‖ ^ d ≤ a / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hmono hC30) h13
    rw [hsplit] at htail
    nlinarith only [hlow, hrev2, htail, hkey, hpos, hC30, hmono]
  -- (12): the upper bound on `G`
  have hzero0 : ∀ (f : ℂ → ℂ) (z : ℂ),
      (∑ v : Fin 0 → Fin 2, ‖PartialWord (List.ofFn v) f z‖) = ‖f z‖ := by
    intro f z
    simp [PartialWord]
  have hGup : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ 1 / 2 →
      ‖H ((t : ℂ) * ζ)‖ ≤ Cp 0 * ‖ζ‖ ^ GammaExp n p := by
    intro ζ hζ0 hζhalf
    have h := hCpb 0 ζ hζ0 hζhalf
    rw [hzero0] at h
    simpa using h
  -- ## (41)
  have h41 : ∀ ξ : ℂ, ‖ξ‖ ≤ t * ρ2 →
      c * ‖ξ‖ ^ GammaExp n p ≤ ‖H ξ‖ ∧ ‖H ξ‖ ≤ Cc * ‖ξ‖ ^ GammaExp n p := by
    intro ξ hξρ
    rcases eq_or_ne ξ 0 with rfl | hξne
    · rw [hH0, norm_zero, Real.zero_rpow (ne_of_gt hγ)]
      simp
    have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξne
    obtain ⟨hxi, hζn, hζ0, hζ1, hζhalf⟩ := hscale ξ hξ0 hξρ
    have hζρ2 : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ≤ ρ2 := by
      rw [hζn, div_le_iff₀ ht]
      have hmul := mul_le_mul_of_nonneg_left hρ2half ht.le
      linarith only [hξρ]
    have hHval : H ξ = H ((t : ℂ) * (((t : ℝ) : ℂ)⁻¹ * ξ)) := by rw [← hxi]
    have hpξ : (0 : ℝ) ≤ ‖ξ‖ ^ GammaExp n p := Real.rpow_nonneg (norm_nonneg ξ) _
    have hpt : (0 : ℝ) < t ^ (-GammaExp n p) := htpow _
    refine ⟨?_, ?_⟩
    · have hlow := hGlow (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζρ2
      rw [hpowe ξ (GammaExp n p)] at hlow
      have hcle : c ≤ a / 2 * t ^ (-GammaExp n p) := by
        rw [hcdef]; exact min_le_left _ _
      rw [hHval]
      nlinarith only [hlow, hcle, hpξ]
    · have hup := hGup (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζhalf
      rw [hpowe ξ (GammaExp n p)] at hup
      have hCle : Cp 0 * t ^ (-GammaExp n p) ≤ Cc := by
        rw [hCcdef]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      rw [hHval]
      nlinarith only [hup, hCle, hpξ]
  -- ## the Jacobian: the order-one dictionary
  have hord1 : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 →
      fderiv ℝ H ((t : ℂ) * ζ) 1
          = ((t : ℝ) : ℂ)⁻¹ * fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1 ∧
        fderiv ℝ H ((t : ℂ) * ζ) Complex.I
          = ((t : ℝ) : ℂ)⁻¹ * fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I := by
    intro ζ h1 h2
    refine ⟨?_, ?_⟩
    · have h := hdict [0] ζ h1 h2
      simpa [PartialWord, List.foldr] using h
    · have h := hdict [1] ζ h1 h2
      simpa [PartialWord, List.foldr] using h
  have hJacH : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 →
      Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ = t ^ 2 * Jac H ((t : ℂ) * ζ) := by
    intro ζ h1 h2
    obtain ⟨e0, e1⟩ := hord1 ζ h1 h2
    have hn0 : ‖DZ H ((t : ℂ) * ζ)‖
        = t⁻¹ * ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := by
      have he : DZ H ((t : ℂ) * ζ)
          = ((t : ℝ) : ℂ)⁻¹ * DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
        simp only [DZ, e0, e1]; ring
      rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hn1 : ‖DZbar H ((t : ℂ) * ζ)‖
        = t⁻¹ * ‖DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := by
      have he : DZbar H ((t : ℂ) * ζ)
          = ((t : ℝ) : ℂ)⁻¹ * DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
        simp only [DZbar, e0, e1]; ring
      rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    simp only [Jac, hn0, hn1]
    field_simp
  -- (16): the upper bound on `J_G`
  have hd1pair : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ 1 / 2 →
      ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1‖
          + ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I‖
        ≤ Cp 1 * ‖ζ‖ ^ (GammaExp n p - 1) := by
    intro ζ h1 h2
    have h := hCpb 1 ζ h1 h2
    have hv0 : ((fun _ : Fin 1 => (0 : Fin 2)) : Fin 1 → Fin 2)
        ≠ (fun _ : Fin 1 => (1 : Fin 2)) := by
      intro hc
      have hcc := congrFun hc 0
      simp at hcc
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({(fun _ : Fin 1 => (0 : Fin 2)),
        (fun _ : Fin 1 => (1 : Fin 2))} : Finset (Fin 1 → Fin 2)))
      (fun i _ _ => norm_nonneg
        (PartialWord (List.ofFn i) (fun z : ℂ => H ((t : ℂ) * z)) ζ))
    rw [Finset.sum_pair hv0] at hle
    have hcast : GammaExp n p - ((1 : ℕ) : ℝ) = GammaExp n p - 1 := by norm_num
    rw [hcast] at h
    have hsimp : ‖PartialWord (List.ofFn (fun _ : Fin 1 => (0 : Fin 2)))
            (fun z : ℂ => H ((t : ℂ) * z)) ζ‖
          + ‖PartialWord (List.ofFn (fun _ : Fin 1 => (1 : Fin 2)))
            (fun z : ℂ => H ((t : ℂ) * z)) ζ‖
        = ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1‖
          + ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I‖ := by
      norm_num [PartialWord]
    rw [hsimp] at hle
    linarith only [hle, h]
  have hJacGup : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ 1 / 2 →
      Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
        ≤ (Cp 1) ^ 2 / 4 * ‖ζ‖ ^ (2 * GammaExp n p - 2) := by
    intro ζ h1 h2
    have hpair := hd1pair ζ h1 h2
    have h3 : ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖
        ≤ 1 / 2 * (Cp 1 * ‖ζ‖ ^ (GammaExp n p - 1)) := by
      have he : DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ
          = (1 / 2 : ℂ) * (fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1
            - Complex.I * fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I) := rfl
      rw [he, norm_mul]
      have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      have h5 : ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1
            - Complex.I * fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I‖
          ≤ ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1‖
            + ‖fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, Complex.norm_I, one_mul]
      rw [h4]
      linarith only [h5, hpair]
    have hnn : (0 : ℝ) ≤ ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := norm_nonneg _
    have hsq : (‖ζ‖ ^ (GammaExp n p - 1)) ^ 2 = ‖ζ‖ ^ (2 * GammaExp n p - 2) := by
      rw [← Real.rpow_natCast (‖ζ‖ ^ (GammaExp n p - 1)) 2,
        ← Real.rpow_mul (norm_nonneg ζ)]
      congr 1
      push_cast
      ring
    have hJle : Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
        ≤ ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2 := by
      simp only [Jac]
      have := sq_nonneg ‖DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ‖
      linarith only [this]
    calc Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
        ≤ ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2 := hJle
      _ ≤ (1 / 2 * (Cp 1 * ‖ζ‖ ^ (GammaExp n p - 1))) ^ 2 := pow_le_pow_left₀ hnn h3 2
      _ = (Cp 1) ^ 2 / 4 * ‖ζ‖ ^ (2 * GammaExp n p - 2) := by rw [← hsq]; ring
  -- (11): the radial derivative of the leading term
  have h11 : ∀ ζ : ℂ, ζ ≠ 0 →
      GammaExp n p * a * ‖ζ‖ ^ (GammaExp n p - 1)
        ≤ ‖HRad (Thm2Term n p A (n + 1)) ζ‖ := by
    intro ζ hζ
    have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hrne : ((‖ζ‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hr
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = Complex.arg ζ := ⟨_, rfl⟩
    have hpolar : ζ = ((‖ζ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hθdef]; exact (Complex.norm_mul_exp_arg_mul_I ζ).symm
    have hdir : ζ / ((‖ζ‖ : ℝ) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := by
      nth_rewrite 1 [hpolar]
      rw [mul_comm, mul_div_assoc, div_self hrne, mul_one]
    obtain ⟨X, hX⟩ : ∃ x : ℂ, x = A (((n + 1 : ℕ)) : ℤ)
        * Complex.exp (((((n + 1 : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ)
          * ((θ : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ y : ℂ, y = ((EpsCoef n (n + 1) p : ℝ) : ℂ)
        * starRingEnd ℂ (A (((n + 1 : ℕ)) : ℤ))
        * Complex.exp (((-(((n + 1 : ℕ)) : ℤ) - (n : ℤ) : ℤ) : ℂ)
          * ((θ : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    have hn1 : ‖X‖ = ‖A ((n : ℤ) + 1)‖ := by
      rw [hX, norm_mul, hexpn _ _, mul_one, hAcast]
    have hn2 : ‖Y‖ = |EpsCoef n (n + 1) p| * ‖A ((n : ℤ) + 1)‖ := by
      rw [hY, norm_mul, norm_mul, hexpn _ _, mul_one, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, hAcast]
    have hprof : a ≤ ‖X + Y‖ := by
      have h := hrev X Y
      rw [hn1, hn2] at h
      rw [hadef]
      linarith only [h]
    have hlam : LambdaCoef n (n + 1) p = GammaExp n p := rfl
    have hgval : ∀ s : ℝ, 0 < s →
        Thm2Term n p A (n + 1) ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          = ((s ^ GammaExp n p : ℝ) : ℂ) * (X + Y) := by
      intro s hs
      have h := (Thm2TermSolvesEq18 n p hn hp (n + 1) (by omega) A).2.1 s hs θ
      rw [h, hlam, hX, hY]
    have hTd : DifferentiableAt ℝ (Thm2Term n p A (n + 1)) ζ :=
      ((Thm2TermSolvesEq18 n p hn hp (n + 1) (by omega) A).1 ζ hζ).differentiableAt
        (by norm_num)
    have hu : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        (Complex.exp ((θ : ℂ) * Complex.I)) ‖ζ‖ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := ‖ζ‖)).mul_const
        (Complex.exp ((θ : ℂ) * Complex.I))
    have hl : HasFDerivAt (Thm2Term n p A (n + 1))
        (fderiv ℝ (Thm2Term n p A (n + 1)) ζ)
        ((fun s : ℝ => (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ‖ζ‖) := by
      show HasFDerivAt _ _ (((‖ζ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      rw [← hpolar]
      exact hTd.hasFDerivAt
    have hderiv1 : HasDerivAt
        (fun s : ℝ => Thm2Term n p A (n + 1) ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fderiv ℝ (Thm2Term n p A (n + 1)) ζ (Complex.exp ((θ : ℂ) * Complex.I))) ‖ζ‖ := by
      have h := hl.comp_hasDerivAt ‖ζ‖ hu
      exact h
    have hderiv2 : HasDerivAt
        (fun s : ℝ => Thm2Term n p A (n + 1) ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (((GammaExp n p * ‖ζ‖ ^ (GammaExp n p - 1) : ℝ) : ℂ) * (X + Y)) ‖ζ‖ := by
      have hR : HasDerivAt (fun s : ℝ => s ^ GammaExp n p)
          (GammaExp n p * ‖ζ‖ ^ (GammaExp n p - 1)) ‖ζ‖ :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hr))
      have hC := (Complex.ofRealCLM.hasFDerivAt
        (x := ‖ζ‖ ^ GammaExp n p)).comp_hasDerivAt ‖ζ‖ hR
      have hbase : HasDerivAt (fun s : ℝ => ((s ^ GammaExp n p : ℝ) : ℂ) * (X + Y))
          (((GammaExp n p * ‖ζ‖ ^ (GammaExp n p - 1) : ℝ) : ℂ) * (X + Y)) ‖ζ‖ := by
        simpa using hC.mul_const (X + Y)
      refine hbase.congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds hr] with s hs
      exact hgval s hs
    have hEq := hderiv1.unique hderiv2
    have hHR : HRad (Thm2Term n p A (n + 1)) ζ
        = ((GammaExp n p * ‖ζ‖ ^ (GammaExp n p - 1) : ℝ) : ℂ) * (X + Y) := by
      show fderiv ℝ (Thm2Term n p A (n + 1)) ζ (ζ / ((‖ζ‖ : ℝ) : ℂ)) = _
      rw [hdir, hEq]
    rw [hHR, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < GammaExp n p * ‖ζ‖ ^ (GammaExp n p - 1) := by
      have := Real.rpow_pos_of_pos hr (GammaExp n p - 1)
      positivity
    rw [abs_of_pos hpos]
    nlinarith only [hprof, hpos]
  -- (18): the lower bound on the radial derivative of `G`
  have hTn0fun : Thm2Term n p A n = fun _ : ℂ => 0 := funext hT0
  have hIccR : ∀ ζ : ℂ, (∑ k ∈ Finset.Icc n (n + 1), HRad (Thm2Term n p A k) ζ)
      = HRad (Thm2Term n p A (n + 1)) ζ := by
    intro ζ
    rw [Finset.sum_Icc_succ_top (by omega : n ≤ n + 1), Finset.Icc_self,
      Finset.sum_singleton]
    have hz : HRad (Thm2Term n p A n) ζ = 0 := by
      simp only [HRad, hTn0fun]
      simp
    rw [hz, zero_add]
  have hGrad : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ ρ2 →
      b * ‖ζ‖ ^ (GammaExp n p - 1)
        ≤ ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := by
    intro ζ hζ0 hζρ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hζhalf : ‖ζ‖ ≤ 1 / 2 := le_trans hζρ hρ2half
    have htail := hC4b ζ hζ0 hζhalf
    rw [hIccR ζ, show n + 1 + 1 = n + 2 from rfl] at htail
    have hsplit : ‖ζ‖ ^ (LambdaCoef n (n + 2) p - 1)
        = ‖ζ‖ ^ (GammaExp n p - 1) * ‖ζ‖ ^ d := by
      rw [← Real.rpow_add hζ0, hddef]
      congr 1
      ring
    have hmono : ‖ζ‖ ^ d ≤ ρ2 ^ d := Real.rpow_le_rpow hζ0.le hζρ hd0.le
    have hpos : (0 : ℝ) < ‖ζ‖ ^ (GammaExp n p - 1) := Real.rpow_pos_of_pos hζ0 _
    have hlow := h11 ζ hζne
    have hrev2 : ‖HRad (Thm2Term n p A (n + 1)) ζ‖
          - ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ
            - HRad (Thm2Term n p A (n + 1)) ζ‖
        ≤ ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := by
      have h0 := norm_add_le (HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ)
        (HRad (Thm2Term n p A (n + 1)) ζ - HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ)
      have h : ‖HRad (Thm2Term n p A (n + 1)) ζ‖
          ≤ ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖
            + ‖HRad (Thm2Term n p A (n + 1)) ζ
              - HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ := by simpa using h0
      rw [norm_sub_rev] at h
      linarith only [h]
    have hkey : C4 * ‖ζ‖ ^ d ≤ b :=
      le_trans (mul_le_mul_of_nonneg_left hmono hC40) h17
    rw [hsplit] at htail
    have hba : b = GammaExp n p * a - b := by rw [hbdef]; ring
    nlinarith only [hlow, hrev2, htail, hkey, hpos, hC40, hmono, hba]
  -- (19) upgraded from almost every to every point
  have hBo : IsOpen ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) :=
    (isOpen_lt continuous_norm continuous_const).sdiff isClosed_singleton
  have hBo' : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hfdcont : ContinuousOn (fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)))
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hBo).mp hSe).2.continuousOn
  have hev1 : ContinuousOn
      (fun ζ : ℂ => fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ 1)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := hfdcont.clm_apply continuousOn_const
  have hev2 : ContinuousOn
      (fun ζ : ℂ => fderiv ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ Complex.I)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := hfdcont.clm_apply continuousOn_const
  have hDZc : ContinuousOn (fun ζ : ℂ => DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) :=
    continuousOn_const.mul (hev1.sub (continuousOn_const.mul hev2))
  have hDZbc : ContinuousOn (fun ζ : ℂ => DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) :=
    continuousOn_const.mul (hev1.add (continuousOn_const.mul hev2))
  have hdirc : ContinuousOn (fun ζ : ℂ => ζ / ((‖ζ‖ : ℝ) : ℂ))
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    refine ContinuousOn.div continuousOn_id
      ((Complex.continuous_ofReal.comp continuous_norm).continuousOn) ?_
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    simpa using norm_pos_iff.mpr hz0
  have hHRc : ContinuousOn (fun ζ : ℂ => HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := hfdcont.clm_apply hdirc
  have hfcont : ContinuousOn (fun ζ : ℂ =>
      Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
        - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2)
      ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    simp only [Jac]
    exact ((hDZc.norm.pow 2).sub (hDZbc.norm.pow 2)).sub
      (continuousOn_const.mul (hHRc.norm.pow 2))
  have hQC := QCDistortionPolar K {ξ : ℂ | ‖ξ‖ < 1}
    (fun z : ℂ => H ((t : ℂ) * z)) hBo' hK hGb hGf.1
  have hQCae : ∀ᵐ ζ : ℂ, ζ ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) →
      0 ≤ Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
        - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2 := by
    filter_upwards [hQC] with ζ h hmem
    have h2 := (h hmem.1 (by simpa using hmem.2)).1.1
    linarith only [h2]
  have hupg : ∀ ζ : ℂ, ζ ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) →
      K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2
        ≤ Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
    intro z0 hz0
    by_contra hcon
    rw [not_le] at hcon
    have hopen : IsOpen (({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)})
        ∩ (fun ζ : ℂ => Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
            - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2) ⁻¹' Set.Iio 0) :=
      hfcont.isOpen_inter_preimage hBo isOpen_Iio
    have hne : (({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)})
        ∩ (fun ζ : ℂ => Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
            - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2) ⁻¹'
          Set.Iio 0).Nonempty := by
      refine ⟨z0, hz0, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Iio]
      linarith only [hcon]
    have hpos := hopen.measure_pos MeasureTheory.volume hne
    rw [MeasureTheory.ae_iff] at hQCae
    have hsubn : (({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)})
        ∩ (fun ζ : ℂ => Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
            - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2) ⁻¹' Set.Iio 0)
        ⊆ {ζ : ℂ | ¬ (ζ ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) →
            0 ≤ Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ
              - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2)} := by
      intro z hz
      intro hc
      have h1 := hc hz.1
      have h2 : Jac (fun z : ℂ => H ((t : ℂ) * z)) z
          - K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) z‖ ^ 2 < 0 := hz.2
      linarith only [h1, h2]
    have hz := MeasureTheory.measure_mono_null hsubn hQCae
    rw [hz] at hpos
    exact absurd hpos (lt_irrefl 0)
  -- (20): the lower bound on `J_G`
  have hJacGlow : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ ρ2 →
      K⁻¹ * b ^ 2 * ‖ζ‖ ^ (2 * GammaExp n p - 2)
        ≤ Jac (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
    intro ζ hζ0 hζρ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hζ1 : ‖ζ‖ < 1 := lt_of_le_of_lt (le_trans hζρ hρ2half) (by norm_num)
    have hmem : ζ ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := ⟨hζ1, by simpa using hζne⟩
    have hu := hupg ζ hmem
    have hg := hGrad ζ hζ0 hζρ
    have hsq : (‖ζ‖ ^ (GammaExp n p - 1)) ^ 2 = ‖ζ‖ ^ (2 * GammaExp n p - 2) := by
      rw [← Real.rpow_natCast (‖ζ‖ ^ (GammaExp n p - 1)) 2,
        ← Real.rpow_mul (norm_nonneg ζ)]
      congr 1
      push_cast
      ring
    have hb2 : (b * ‖ζ‖ ^ (GammaExp n p - 1)) ^ 2
        ≤ ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hg 2
    have hKinv : (0 : ℝ) < K⁻¹ := inv_pos.mpr hK0
    have hstep : K⁻¹ * (b * ‖ζ‖ ^ (GammaExp n p - 1)) ^ 2
        ≤ K⁻¹ * ‖HRad (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 hKinv.le
    have heq : K⁻¹ * (b * ‖ζ‖ ^ (GammaExp n p - 1)) ^ 2
        = K⁻¹ * b ^ 2 * ‖ζ‖ ^ (2 * GammaExp n p - 2) := by
      rw [← hsq]; ring
    linarith only [hu, hstep, heq.symm.le, heq.le]
  -- ## (42)
  have h42 : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ t * ρ2 →
      c * ‖ξ‖ ^ (2 * GammaExp n p - 2) ≤ Jac H ξ ∧
        Jac H ξ ≤ Cc * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by
    intro ξ hξ0 hξρ
    obtain ⟨hxi, hζn, hζ0, hζ1, hζhalf⟩ := hscale ξ hξ0 hξρ
    have hζρ2 : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ≤ ρ2 := by
      rw [hζn, div_le_iff₀ ht]
      have hmul := mul_le_mul_of_nonneg_left hρ2half ht.le
      linarith only [hξρ]
    have hJ := hJacH (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζ1
    rw [← hxi] at hJ
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have hpξ : (0 : ℝ) ≤ ‖ξ‖ ^ (2 * GammaExp n p - 2) :=
      Real.rpow_nonneg (norm_nonneg ξ) _
    have hpowξ : ‖((t : ℝ) : ℂ)⁻¹ * ξ‖ ^ (2 * GammaExp n p - 2)
        = t ^ (-(2 * GammaExp n p - 2)) * ‖ξ‖ ^ (2 * GammaExp n p - 2) :=
      hpowe ξ (2 * GammaExp n p - 2)
    have ht2eq : (t ^ 2)⁻¹ * t ^ (-(2 * GammaExp n p - 2))
        = t ^ (-(2 * GammaExp n p)) := by
      have h1 : ((t : ℝ) ^ (2 : ℕ))⁻¹ = t ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg ht.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
      rw [h1, ← Real.rpow_add ht]
      congr 1
      ring
    refine ⟨?_, ?_⟩
    · have hlow := hJacGlow (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζρ2
      rw [hpowξ, hJ] at hlow
      have hcle : c ≤ K⁻¹ * b ^ 2 * t ^ (-(2 * GammaExp n p)) := by
        rw [hcdef]; exact min_le_right _ _
      have hkey : K⁻¹ * b ^ 2 * (t ^ (-(2 * GammaExp n p - 2))
            * ‖ξ‖ ^ (2 * GammaExp n p - 2))
          ≤ t ^ 2 * Jac H ξ := hlow
      have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr ht2))
      rw [inv_mul_cancel_left₀ (ne_of_gt ht2)] at hmul
      have heq2 : (t ^ 2)⁻¹ * (K⁻¹ * b ^ 2 * (t ^ (-(2 * GammaExp n p - 2))
            * ‖ξ‖ ^ (2 * GammaExp n p - 2)))
          = K⁻¹ * b ^ 2 * t ^ (-(2 * GammaExp n p)) * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by
        rw [← ht2eq]; ring
      rw [heq2] at hmul
      nlinarith only [hmul, hcle, hpξ]
    · have hup := hJacGup (((t : ℝ) : ℂ)⁻¹ * ξ) hζ0 hζhalf
      rw [hpowξ, hJ] at hup
      have hCle : (Cp 1) ^ 2 / 4 * t ^ (-(2 * GammaExp n p)) ≤ Cc := by
        rw [hCcdef]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      have hmul := mul_le_mul_of_nonneg_left hup (le_of_lt (inv_pos.mpr ht2))
      rw [inv_mul_cancel_left₀ (ne_of_gt ht2)] at hmul
      have heq2 : (t ^ 2)⁻¹ * ((Cp 1) ^ 2 / 4 * (t ^ (-(2 * GammaExp n p - 2))
            * ‖ξ‖ ^ (2 * GammaExp n p - 2)))
          = (Cp 1) ^ 2 / 4 * t ^ (-(2 * GammaExp n p)) * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by
        rw [← ht2eq]; ring
      rw [heq2] at hmul
      nlinarith only [hmul, hCle, hpξ]
  exact ⟨t * ρ2, by positivity, c, Cc, hc0, hcC, Cmf, hHsm.mono hsub, h41, h42, h43, h44⟩
