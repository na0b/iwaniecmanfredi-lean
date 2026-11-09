import IwaniecManfredi.Thm2Term
import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.LambdaEpsEstimates
import IwaniecManfredi.WirtingerModulusPowerRule
import IwaniecManfredi.WirtingerProductRule
import IwaniecManfredi.WirtingerPowerRule
import IwaniecManfredi.WirtingerConjRule
import IwaniecManfredi.Thm2TermWirtingerDerivs
import IwaniecManfredi.WeakPartialAcrossPoint
import IwaniecManfredi.PowerIntegrableNearZero

/-- Each summand of the series (19) is itself a solution of (18), and is
`r^{λ_k}` times a trigonometric profile of frequencies `k - n` and `-k - n`.
Since solving (18) is an identity between the *weak* Wirtinger derivatives,
part (c) also carries the statement that `T_k` has weak first derivatives on
the disc: they are its classical ones, which is `WeakPartialAcrossPoint` at
the single exceptional point `0`, the growth exponent being `β = 0` because
`λ_k ≥ 0` makes `T_k` bounded there, and `|∇T_k| = O(|ξ|^{λ_k-1}) = O(|ξ|^{-1})`
is locally integrable.
This is the paper's "our arguments can be turned back" at line 357, which is
the entire content of the converse half of Theorem 2.  The computation is the
same `(2λ_k + p(n-k))(λ_k + n + k) = (2-p)(n+k)(λ_k + n - k)` algebra over the
indicial equation that the compatibility relations use, so no square root is
unfolded; and it needs no restriction on `p`. -/
theorem Thm2TermSolvesEq18 (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (k : ℕ) (hk : n ≤ k)
    (A : ℤ → ℂ) :
    (∀ ξ : ℂ, ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (Thm2Term n p A k) ξ) ∧
    (∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ((r ^ LambdaCoef n k p : ℝ) : ℂ)
            * (A (k : ℤ) * Complex.exp ((((k : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                  * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) ∧
    SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} (Thm2Term n p A k) := by
  have hk1 : 1 ≤ k := le_trans hn hk
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  -- ## Step 0: `L ≥ 0` and `L + n + k > 0`
  have hL0 : 0 ≤ LambdaCoef n k p := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [← h, (LambdaEpsEstimates n p hn hp).1]
    · have hlow := ((LambdaEpsEstimates n p hn hp).2.2.2 k (by omega)).1
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := by
        have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
        exact div_pos (by linarith) hnp
      linarith
  have hLnk : 0 < LambdaCoef n k p + (n : ℝ) + (k : ℝ) := by linarith
  -- ## Step 2: part (a), smoothness away from the origin
  have hconjsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) :=
    Complex.conjCLE.contDiff
  have hFsmooth : ∀ ξ : ℂ, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => A (k : ℤ) * z ^ k
        + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ z) ^ k) ξ := by
    intro ξ
    refine ContDiffAt.add ?_ ?_
    · exact contDiffAt_const.mul ((contDiff_id.pow k).contDiffAt)
    · exact contDiffAt_const.mul ((hconjsmooth.pow k).contDiffAt)
  have hGsmooth : ∀ ξ : ℂ, ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) ξ :=
    fun ξ hξ => (WirtingerModulusPowerRule (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) ξ hξ).1
  have hHsmooth : ∀ ξ : ℂ, ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ (-(n : ℤ))) ξ := by
    intro ξ hξ
    have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ n) ξ := (contDiff_id.pow n).contDiffAt
    have h := hb.inv (by simpa using pow_ne_zero n hξ)
    simpa [zpow_neg, zpow_natCast, Pi.inv_def] using h
  have hA : ∀ ξ : ℂ, ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (Thm2Term n p A k) ξ := by
    intro ξ hξ
    exact ((hFsmooth ξ).mul (hGsmooth ξ hξ)).mul (hHsmooth ξ hξ)
  -- ## Step 1: part (b), the polar form
  have hB : ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ((r ^ LambdaCoef n k p : ℝ) : ℂ)
            * (A (k : ℤ) * Complex.exp ((((k : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                  * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ)
                      * (θ : ℂ) * Complex.I)) := by
    intro r hr θ
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
    have hang1 : Complex.exp ((θ : ℂ) * Complex.I) ^ k
          * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        = Complex.exp ((((k : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hang2 : (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ k
          * Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ))
        = Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
      rw [hconjE, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [Thm2Term, hnorm, hconjxi, mul_pow, mul_zpow]
    rw [← hang1, ← hang2, ← hrcomb]
    ring
  -- ## Step 3: the two Wirtinger derivatives of `T_k`, in closed form
  have hDZT := fun (ξ : ℂ) (hξ : ξ ≠ 0) => Thm2TermWirtingerDerivs n p A k ξ hξ
  have hconjDZT : ∀ ξ : ℂ, ξ ≠ 0 →
      starRingEnd ℂ (DZ (Thm2Term n p A k) ξ)
        = (((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
              * (starRingEnd ℂ ξ) ^ (-(n : ℤ)) / starRingEnd ℂ ξ)
          * ((k : ℂ) * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)
            + (((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ))
                * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k
                  + ((EpsCoef n k p : ℝ) : ℂ) * (A (k : ℤ) * ξ ^ k))) := by
    intro ξ hξ
    rw [(hDZT ξ hξ).1]
    simp only [map_mul, map_div₀, map_add, map_sub, map_pow, map_zpow₀, map_natCast,
      Complex.conj_ofReal, Complex.conj_conj, map_ofNat]
  have hyn : ∀ ξ : ℂ, ξ ≠ 0 →
      ((starRingEnd ℂ ξ) ^ n / ξ ^ n) * (starRingEnd ℂ ξ) ^ (-(n : ℤ)) = ξ ^ (-(n : ℤ)) := by
    intro ξ hξ
    have hyne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    field_simp
  -- ## Step 0 (continued): the indicial equation (I)
  have hp0 : (0 : ℝ) ≤ p - 1 := by linarith
  have hpne : p ≠ 0 := by positivity
  have hLnkne : LambdaCoef n k p + (n : ℝ) + (k : ℝ) ≠ 0 := ne_of_gt hLnk
  have hrad : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
    have h1 : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) := mul_nonneg (by positivity) hp0
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 := by positivity
    linarith
  have hS : Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) ^ 2
      = 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := Real.sq_sqrt hrad
  have hind : LambdaCoef n k p ^ 2 + p * (n : ℝ) * LambdaCoef n k p
      + ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) = 0 := by
    simp only [LambdaCoef]
    linear_combination hS / 4
  -- ## Step 7: the identity `(α)`
  have hcore : p * ((LambdaCoef n k p + (n : ℝ)) ^ 2 - (k : ℝ) ^ 2)
      = (p - 2) * (LambdaCoef n k p ^ 2 + (k : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
    linear_combination 2 * hind
  have halpha : (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2
      = (1 / 2 - 1 / p) * ((k : ℝ)
          + ((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ))
            * (1 + EpsCoef n k p)) := by
    simp only [EpsCoef]
    field_simp
    linear_combination hcore + 2 * hind
  -- ## Step 6: the identity `(β)`, from `(α)`
  have hbeta : EpsCoef n k p * ((k : ℝ) + (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2)
      = (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 := by
    simp only [EpsCoef]
    field_simp
    ring
  have halphaC : ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2
      = ((1 / 2 - 1 / p : ℝ) : ℂ) * ((k : ℂ)
          + (((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ))
            * (1 + ((EpsCoef n k p : ℝ) : ℂ))) := by
    exact_mod_cast congrArg Complex.ofReal halpha
  have hbetaC : ((EpsCoef n k p : ℝ) : ℂ)
        * ((k : ℂ) + ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2)
      = ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 := by
    exact_mod_cast congrArg Complex.ofReal hbeta
  -- ## Step 5: the algebraic core of the reduction of (18)
  have halg : ∀ (gg P Py x y Cc K N Mu Ee u v Q : ℂ), x ≠ 0 → y ≠ 0 →
      Q * Py = P →
      Mu / 2 = Cc * (K + (Mu / 2 - N) * (1 + Ee)) →
      Ee * (K + Mu / 2) = Mu / 2 →
      (gg * P / y) * (K * (Ee * v) + (Mu / 2) * (u + Ee * v))
        = Cc * ((x / y) * ((gg * P / x) * (K * u + (Mu / 2 - N) * (u + Ee * v)))
            + Q * ((gg * Py / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)))) := by
    intro gg P Py x y Cc K N Mu Ee u v Q hx hy hQ h1 h2
    have e1 : (x / y) * ((gg * P / x) * (K * u + (Mu / 2 - N) * (u + Ee * v)))
        = (gg * P / y) * (K * u + (Mu / 2 - N) * (u + Ee * v)) := by
      field_simp
    have e2 : Q * ((gg * Py / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)))
        = (gg * P / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)) := by
      rw [show Q * ((gg * Py / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)))
          = ((Q * Py) * gg / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)) from by ring, hQ]
      ring
    rw [e1, e2, show Cc * ((gg * P / y) * (K * u + (Mu / 2 - N) * (u + Ee * v))
          + (gg * P / y) * (K * v + (Mu / 2 - N) * (v + Ee * u)))
        = (gg * P / y) * (Cc * ((K * u + (Mu / 2 - N) * (u + Ee * v))
            + (K * v + (Mu / 2 - N) * (v + Ee * u)))) from by ring]
    congr 1
    linear_combination (u + v) * h1 + v * h2
  -- ## Step 8: the pointwise form of (18)
  have hpointwise : ∀ ξ : ℂ, ξ ≠ 0 →
      DZbar (Thm2Term n p A k) ξ
        = ((1 / 2 - 1 / p : ℝ) : ℂ) *
          ((ξ / starRingEnd ℂ ξ) * DZ (Thm2Term n p A k) ξ
            + ((starRingEnd ℂ ξ) ^ n / ξ ^ n)
                * starRingEnd ℂ (DZ (Thm2Term n p A k) ξ)) := by
    intro ξ hξ
    have hyne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
    rw [(hDZT ξ hξ).2, hconjDZT ξ hξ, (hDZT ξ hξ).1]
    exact halg _ _ _ ξ (starRingEnd ℂ ξ) _ (k : ℂ) (n : ℂ) _ _ _ _ _
      hξ hyne (hyn ξ hξ) halphaC hbetaC
  -- ## Step 9: growth bounds for `T_k` and its first derivatives
  have hCA : (0 : ℝ) ≤ ‖A (k : ℤ)‖ := norm_nonneg _
  have habs : (0 : ℝ) ≤ |EpsCoef n k p| := abs_nonneg _
  have hcombrpow : ∀ r : ℝ, 0 < r →
      r ^ (k : ℝ) * r ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * r ^ (-(n : ℝ))
        = r ^ LambdaCoef n k p := by
    intro r hrr
    rw [← Real.rpow_add hrr, ← Real.rpow_add hrr]
    congr 1
    ring
  have hgnorm : ∀ ξ : ℂ, ξ ≠ 0 →
      ‖((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)‖
        = ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) := by
    intro ξ hξ
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) _)]
  have hpnorm : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ ^ (-(n : ℤ))‖ = ‖ξ‖ ^ (-(n : ℝ)) := by
    intro ξ hξ
    rw [norm_zpow, ← Real.rpow_intCast ‖ξ‖ (-(n : ℤ))]
    norm_num
  have hunorm : ∀ ξ : ℂ, ‖A (k : ℤ) * ξ ^ k‖ = ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
    intro ξ
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖ξ‖ k]
  have hvnorm : ∀ ξ : ℂ,
      ‖starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k‖
        = ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
    intro ξ
    rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj,
      ← Real.rpow_natCast ‖ξ‖ k]
  have hEnorm : ‖((EpsCoef n k p : ℝ) : ℂ)‖ = |EpsCoef n k p| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hthree : ∀ ξ : ℂ,
      ‖A (k : ℤ) * ξ ^ k‖
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) ∧
      ‖((EpsCoef n k p : ℝ) : ℂ)
            * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) ∧
      ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ)
            * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
    intro ξ
    have hrk : (0 : ℝ) ≤ ‖ξ‖ ^ (k : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have h1 : ‖A (k : ℤ) * ξ ^ k‖ = ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := hunorm ξ
    have h2 : ‖((EpsCoef n k p : ℝ) : ℂ)
          * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)‖
        = |EpsCoef n k p| * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) := by
      rw [norm_mul, hvnorm ξ, hEnorm]
    have hprod : (0 : ℝ) ≤ ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := mul_nonneg hCA hrk
    have hone' : (1 : ℝ) ≤ 1 + |EpsCoef n k p| := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      calc ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) = 1 * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) := by ring
        _ ≤ (1 + |EpsCoef n k p|) * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hone' hprod
        _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by ring
    · rw [h2]
      calc |EpsCoef n k p| * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ))
          ≤ (1 + |EpsCoef n k p|) * (‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hprod
        _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by ring
    · refine le_trans (norm_add_le _ _) ?_
      rw [h1, h2]
      exact le_of_eq (by ring)
  have hbdgen : ∀ (c1 c2 X1 X2 : ℂ) (W : ℝ), ‖X1‖ ≤ W → ‖X2‖ ≤ W →
      ‖c1 * X1 + c2 * X2‖ ≤ (‖c1‖ + ‖c2‖) * W := by
    intro c1 c2 X1 X2 W h1 h2
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have k1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg c1)
    have k2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg c2)
    have hexp : (‖c1‖ + ‖c2‖) * W = ‖c1‖ * W + ‖c2‖ * W := by ring
    rw [hexp]
    linarith
  have hnMuN : ‖((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ)‖
      = |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)| := by
    rw [show ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ)
        = (((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ) : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have hnMuh : ‖((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2‖
      = |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2| := by
    rw [show ((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2
        = (((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have hCBpos : (0 : ℝ) ≤ ((k : ℝ) + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)|
      + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2|)
      * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) := by positivity
  have hTnorm : ∀ ξ : ℂ, ξ ≠ 0 →
      ‖Thm2Term n p A k ξ‖
        ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ LambdaCoef n k p := by
    intro ξ hξ
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hrk : (0 : ℝ) ≤ ‖ξ‖ ^ (k : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hmu : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hnn : (0 : ℝ) ≤ ‖ξ‖ ^ (-(n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hF : ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ ξ) ^ k‖
        ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by
      have h := (hthree ξ).2.2
      rw [show ((EpsCoef n k p : ℝ) : ℂ) * (starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ ξ) ^ k)
        = ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ ξ) ^ k from by ring] at h
      exact h
    calc ‖Thm2Term n p A k ξ‖
        = ‖A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ ξ) ^ k‖
            * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) := by
          simp only [Thm2Term]
          rw [norm_mul, norm_mul, hgnorm ξ hξ, hpnorm ξ hξ]
      _ ≤ ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ))
            * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) := by
          gcongr
      _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖
            * (‖ξ‖ ^ (k : ℝ) * ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ))
              * ‖ξ‖ ^ (-(n : ℝ))) := by ring
      _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ LambdaCoef n k p := by
          rw [hcombrpow ‖ξ‖ hr]
  have hT0 : Thm2Term n p A k 0 = 0 := by
    simp only [Thm2Term]
    rw [zpow_neg, zpow_natCast, zero_pow (by omega : n ≠ 0), inv_zero, mul_zero]
  have hTbd : ∀ ξ : ℂ, ‖ξ‖ < 1 →
      ‖Thm2Term n p A k ξ‖ ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ := by
    intro ξ hξ1
    by_cases hξ : ξ = 0
    · rw [hξ, hT0, norm_zero]
      positivity
    · refine le_trans (hTnorm ξ hξ) ?_
      have h1 : ‖ξ‖ ^ LambdaCoef n k p ≤ 1 :=
        Real.rpow_le_one (norm_nonneg _) hξ1.le hL0
      have h2 : (0 : ℝ) ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ := by positivity
      calc (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ LambdaCoef n k p
          ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * 1 := mul_le_mul_of_nonneg_left h1 h2
        _ = (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ := by ring
  have hDbd : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      ‖DZ (Thm2Term n p A k) ξ‖
          ≤ ((k : ℝ) + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)|
              + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2|)
            * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) / ‖ξ‖ ∧
      ‖DZbar (Thm2Term n p A k) ξ‖
          ≤ ((k : ℝ) + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)|
              + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2|)
            * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) / ‖ξ‖ := by
    intro ξ hξ hξ1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hyne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
    have hynorm : ‖starRingEnd ℂ ξ‖ = ‖ξ‖ := Complex.norm_conj ξ
    have hrk : (0 : ℝ) ≤ ‖ξ‖ ^ (k : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hmu : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hnn : (0 : ℝ) ≤ ‖ξ‖ ^ (-(n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hW : (0 : ℝ) ≤ (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ) := by positivity
    have hfacx : ‖((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
          * ξ ^ (-(n : ℤ)) / ξ‖
        = ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ := by
      rw [norm_div, norm_mul, hgnorm ξ hξ, hpnorm ξ hξ]
    have hfacy : ‖((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
          * ξ ^ (-(n : ℤ)) / starRingEnd ℂ ξ‖
        = ‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖ := by
      rw [norm_div, norm_mul, hgnorm ξ hξ, hpnorm ξ hξ, hynorm]
    have htail : ∀ CC : ℝ, 0 ≤ CC →
        (‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖)
            * (CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)))
          ≤ CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) / ‖ξ‖ := by
      intro CC hCC
      have hid : (‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) * ‖ξ‖ ^ (-(n : ℝ)) / ‖ξ‖)
            * (CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ * ‖ξ‖ ^ (k : ℝ)))
          = CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) * ‖ξ‖ ^ LambdaCoef n k p / ‖ξ‖ := by
        rw [← hcombrpow ‖ξ‖ hr]
        field_simp
      rw [hid]
      have h1 : ‖ξ‖ ^ LambdaCoef n k p ≤ 1 :=
        Real.rpow_le_one (norm_nonneg _) hξ1.le hL0
      have h2 : (0 : ℝ) ≤ CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) := by positivity
      have hnum : CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) * ‖ξ‖ ^ LambdaCoef n k p
          ≤ CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) := by
        calc CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) * ‖ξ‖ ^ LambdaCoef n k p
            ≤ CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) * 1 :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = CC * ((1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖) := by ring
      exact div_le_div_of_nonneg_right hnum hr.le
    refine ⟨?_, ?_⟩
    · rw [(hDZT ξ hξ).1, norm_mul, hfacx]
      refine le_trans ?_ (htail _ (by positivity))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (hbdgen _ _ _ _ _ (hthree ξ).1 (hthree ξ).2.2) ?_
      rw [Complex.norm_natCast, hnMuN]
      exact mul_le_mul_of_nonneg_right
        (by linarith [abs_nonneg ((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2)]) hW
    · rw [(hDZT ξ hξ).2, norm_mul, hfacy]
      refine le_trans ?_ (htail _ (by positivity))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (hbdgen _ _ _ _ _ (hthree ξ).2.1 (hthree ξ).2.2) ?_
      rw [Complex.norm_natCast, hnMuh]
      exact mul_le_mul_of_nonneg_right
        (by linarith [abs_nonneg ((LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ))]) hW
  refine ⟨hA, hB, ?_⟩
  set MM : ℝ := (1 + |EpsCoef n k p|) * ‖A (k : ℤ)‖ with hMMdef
  set CC : ℝ := ((k : ℝ) + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2 - (n : ℝ)|
      + |(LambdaCoef n k p + (n : ℝ) - (k : ℝ)) / 2|) * MM with hCCdef
  have hMM0 : (0 : ℝ) ≤ MM := by rw [hMMdef]; positivity
  have hCC0 : (0 : ℝ) ≤ CC := by rw [hCCdef]; positivity
  -- ## Step 10: the weak first partial derivatives of `T_k` on `𝔹`
  have hBopen : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hball : Metric.ball (0 : ℂ) 1 = {ξ : ℂ | ‖ξ‖ < 1} := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have hS0 : ({0} : Set ℂ) ⊆ {ξ : ℂ | ‖ξ‖ < 1} := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    simp [hz]
  have hSfin : ∀ Kc ⊆ {ξ : ℂ | ‖ξ‖ < 1}, IsCompact Kc →
      (({0} : Set ℂ) ∩ Kc).Finite := fun Kc _ _ => (Set.finite_singleton 0).inter_of_left _
  have hfxy : ∀ z : ℂ,
      fderiv ℝ (Thm2Term n p A k) z 1
          = DZ (Thm2Term n p A k) z + DZbar (Thm2Term n p A k) z ∧
      fderiv ℝ (Thm2Term n p A k) z Complex.I
          = Complex.I * (DZ (Thm2Term n p A k) z - DZbar (Thm2Term n p A k) z) := by
    intro z
    refine ⟨by simp only [DZ, DZbar]; ring, ?_⟩
    simp only [DZ, DZbar]
    linear_combination (fderiv ℝ (Thm2Term n p A k) z Complex.I) * Complex.I_mul_I
  have hPW : ∀ (j : Fin 2) (z : ℂ), PartialWord [j] (Thm2Term n p A k) z
      = fderiv ℝ (Thm2Term n p A k) z (if j = 0 then 1 else Complex.I) := by
    intro j z
    rfl
  have hTmeas : Measurable (Thm2Term n p A k) := by
    have h1 : Continuous (fun z : ℂ => A (k : ℤ) * z ^ k
        + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ z) ^ k) := by
      exact (continuous_const.mul (continuous_id.pow k)).add
        (continuous_const.mul ((Complex.continuous_conj).pow k))
    have h2 : Measurable
        (fun z : ℂ => ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) := by
      refine Complex.measurable_ofReal.comp ?_
      exact (continuous_norm.measurable).pow measurable_const
    have h3 : Measurable (fun z : ℂ => z ^ (-(n : ℤ))) := by
      have : (fun z : ℂ => z ^ (-(n : ℤ))) = fun z : ℂ => (z ^ n)⁻¹ := by
        funext z; rw [zpow_neg, zpow_natCast]
      rw [this]
      exact (measurable_id.pow_const n).inv
    exact (h1.measurable.mul h2).mul h3
  have hPWmeas : ∀ j : Fin 2, Measurable (PartialWord [j] (Thm2Term n p A k)) := by
    intro j
    have h : Measurable (fun z : ℂ =>
        fderiv ℝ (Thm2Term n p A k) z (if j = 0 then 1 else Complex.I)) :=
      measurable_fderiv_apply_const ℝ (Thm2Term n p A k) (if j = 0 then 1 else Complex.I)
    exact (funext (hPW j) : PartialWord [j] (Thm2Term n p A k) = _) ▸ h
  have hPWbd : ∀ (j : Fin 2) (ξ : ℂ), ξ ≠ 0 → ‖ξ‖ < 1 →
      ‖PartialWord [j] (Thm2Term n p A k) ξ‖ ≤ 2 * CC / ‖ξ‖ := by
    intro j ξ hξ hξ1
    obtain ⟨hd1, hd2⟩ := hDbd ξ hξ hξ1
    rw [hPW j ξ]
    by_cases hj : j = 0
    · rw [if_pos hj, (hfxy ξ).1]
      calc ‖DZ (Thm2Term n p A k) ξ + DZbar (Thm2Term n p A k) ξ‖
          ≤ ‖DZ (Thm2Term n p A k) ξ‖ + ‖DZbar (Thm2Term n p A k) ξ‖ := norm_add_le _ _
        _ ≤ 2 * CC / ‖ξ‖ := by
            rw [show 2 * CC / ‖ξ‖ = CC / ‖ξ‖ + CC / ‖ξ‖ from by ring]
            linarith
    · rw [if_neg hj, (hfxy ξ).2, norm_mul, Complex.norm_I, one_mul]
      calc ‖DZ (Thm2Term n p A k) ξ - DZbar (Thm2Term n p A k) ξ‖
          ≤ ‖DZ (Thm2Term n p A k) ξ‖ + ‖DZbar (Thm2Term n p A k) ξ‖ := norm_sub_le _ _
        _ ≤ 2 * CC / ‖ξ‖ := by
            rw [show 2 * CC / ‖ξ‖ = CC / ‖ξ‖ + CC / ‖ξ‖ from by ring]
            linarith
  have hne0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    simp
  have hballfin : MeasureTheory.volume (Metric.ball (0 : ℂ) 1) ≠ ⊤ :=
    ne_of_lt MeasureTheory.measure_ball_lt_top
  have hbound1 : MeasureTheory.Integrable
      ((Metric.ball (0 : ℂ) 1).indicator (fun _ : ℂ => MM)) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_ball).mpr
      (MeasureTheory.integrableOn_const hballfin (by simp))
  have hpow1 : MeasureTheory.IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(1 : ℝ)))
      (Metric.ball (0 : ℂ) 1) MeasureTheory.volume := by
    have h := PowerIntegrableNearZero 1 one_pos le_rfl 1 one_pos 1 le_rfl (by norm_num)
    rw [show ((1 : ℝ) - 2) * 1 = -(1 : ℝ) from by norm_num] at h
    exact h
  have hbound2 : MeasureTheory.Integrable
      ((Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => 2 * CC * ‖z‖ ^ (-(1 : ℝ))))
      MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_ball).mpr (hpow1.const_mul _)
  have hgloc : MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} (Thm2Term n p A k) := by
    intro Kc hKc hKcc
    rw [MeasureTheory.memLp_one_iff_integrable]
    refine MeasureTheory.Integrable.mono' hbound1
      (hTmeas.indicator hKcc.measurableSet).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z ∈ Kc
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (by rw [hball]; exact hKc hz)]
      exact hTbd z (hKc hz)
    · rw [Set.indicator_of_notMem hz, norm_zero]
      by_cases hz2 : z ∈ Metric.ball (0 : ℂ) 1
      · rw [Set.indicator_of_mem hz2]
        exact hMM0
      · rw [Set.indicator_of_notMem hz2]
  have hvloc : ∀ j : Fin 2,
      MemLpLocOn 1 {ξ : ℂ | ‖ξ‖ < 1} (PartialWord [j] (Thm2Term n p A k)) := by
    intro j Kc hKc hKcc
    rw [MeasureTheory.memLp_one_iff_integrable]
    refine MeasureTheory.Integrable.mono' hbound2
      ((hPWmeas j).indicator hKcc.measurableSet).aestronglyMeasurable ?_
    filter_upwards [hne0] with z hz
    by_cases hzK : z ∈ Kc
    · rw [Set.indicator_of_mem hzK, Set.indicator_of_mem (by rw [hball]; exact hKc hzK)]
      have hb := hPWbd j z hz (hKc hzK)
      rw [Real.rpow_neg_one]
      rw [show 2 * CC * ‖z‖⁻¹ = 2 * CC / ‖z‖ from by ring]
      exact hb
    · rw [Set.indicator_of_notMem hzK, norm_zero]
      by_cases hz2 : z ∈ Metric.ball (0 : ℂ) 1
      · rw [Set.indicator_of_mem hz2]
        positivity
      · rw [Set.indicator_of_notMem hz2]
  have hgC1 : ContDiffOn ℝ (1 : ℕ) (Thm2Term n p A k) ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h
      exact hx.2 (by rw [h]; exact Set.mem_singleton 0)
    exact ((hA x hxne).of_le (by simp)).contDiffWithinAt
  have hweak : ∀ j : Fin 2, IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} j (Thm2Term n p A k)
      (PartialWord [j] (Thm2Term n p A k)) := by
    intro j
    refine WeakPartialAcrossPoint {ξ : ℂ | ‖ξ‖ < 1} hBopen {0} hS0 hSfin j
      (Thm2Term n p A k) (PartialWord [j] (Thm2Term n p A k)) 0 le_rfl (by norm_num)
      hgC1 (fun z _ => rfl) hgloc (hvloc j) ?_
    intro z₀ hz₀
    rw [Set.mem_singleton_iff] at hz₀
    subst hz₀
    refine ⟨MM, 1, one_pos, ?_⟩
    intro z hz1 hz2
    rw [sub_zero] at hz1 hz2 ⊢
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact hTbd z hz2
  -- ## Step 11: conclusion
  refine ⟨DZ (Thm2Term n p A k), DZbar (Thm2Term n p A k), ?_, ?_⟩
  · exact ⟨PartialWord [0] (Thm2Term n p A k), PartialWord [1] (Thm2Term n p A k),
      hgloc, hvloc 0, hvloc 1, hweak 0, hweak 1, fun z => rfl, fun z => rfl⟩
  · exact Filter.Eventually.of_forall (fun ξ _ hξ => hpointwise ξ hξ)
