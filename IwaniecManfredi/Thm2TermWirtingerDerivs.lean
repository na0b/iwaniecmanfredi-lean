import IwaniecManfredi.Thm2Term
import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar
import IwaniecManfredi.WirtingerModulusPowerRule
import IwaniecManfredi.WirtingerProductRule
import IwaniecManfredi.WirtingerPowerRule
import IwaniecManfredi.WirtingerConjRule
set_option maxHeartbeats 1000000

/-- The two Wirtinger derivatives of a single summand of the series (19), in
closed form off the origin.

`T_k(ξ) = (A_k ξ^k + ε_k conj(A_k) conj(ξ)^k) |ξ|^{λ_k + n - k} ξ^{-n}` is a
product of three factors, each smooth on `ℂ - {0}`, so the Wirtinger product
rule applies; the power rule handles `ξ^k` and `ξ^{-n}`, the conjugation rule
handles `conj(ξ)^k`, and the modulus-power rule handles `|ξ|^s` with
`s = λ_k + n - k`.  Collecting the terms gives

`T_k,ξ   = (|ξ|^s ξ^{-n}/ξ) (k A_k ξ^k + (s/2 - n)(A_k ξ^k + ε_k conj(A_k) conj(ξ)^k))`,
`T_k,ξ̄  = (|ξ|^s ξ^{-n}/conj ξ) (k ε_k conj(A_k) conj(ξ)^k + (s/2)(A_k ξ^k + ε_k conj(A_k) conj(ξ)^k))`.

These are the Cartesian form of the paper's polar transformation formulas
`H_ξ̄ = ½(H_r + (i/r)H_θ)e^{iθ}` and `H_ξ = ½(H_r - (i/r)H_θ)e^{-iθ}` at
`paper.tex:234-237`, specialised to the summand, and they are what every later
use of (18) on a single term reads.

No constraint whatever is imposed on `n`, `p` or `k`: the identity is a formal
differentiation of a product of integer and real powers, valid off the origin
for every exponent.  In particular neither `1 ≤ n`, nor `1 < p`, nor `n ≤ k`
is needed, which matters because one consumer quantifies over every `k : ℕ`
with no lower bound. -/
theorem Thm2TermWirtingerDerivs (n : ℕ) (p : ℝ) (A : ℤ → ℂ) (k : ℕ) (ξ : ℂ) (hξ : ξ ≠ 0) :
    DZ (Thm2Term n p A k) ξ
      = (((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * ξ ^ (-(n : ℤ)) / ξ)
        * ((k : ℂ) * (A (k : ℤ) * ξ ^ k)
          + (((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2 - (n : ℂ))
              * (A (k : ℤ) * ξ ^ k
                + ((EpsCoef n k p : ℝ) : ℂ)
                    * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k)))
    ∧ DZbar (Thm2Term n p A k) ξ
      = (((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * ξ ^ (-(n : ℤ))
            / starRingEnd ℂ ξ)
        * ((k : ℂ) * (((EpsCoef n k p : ℝ) : ℂ)
              * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k))
          + (((LambdaCoef n k p + (n : ℝ) - (k : ℝ) : ℝ) : ℂ) / 2)
              * (A (k : ℤ) * ξ ^ k
                + ((EpsCoef n k p : ℝ) : ℂ)
                    * (starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ ξ) ^ k))) := by
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΩ0 : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hidC : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => z) {z : ℂ | z ≠ 0} :=
    contDiff_id.contDiffOn
  have hidne : ∀ ζ ∈ {z : ℂ | z ≠ 0}, (fun z : ℂ => z) ζ ≠ 0 := fun ζ hζ => hζ
  have hconjsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) :=
    Complex.conjCLE.contDiff
  have hconjC : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) {z : ℂ | z ≠ 0} :=
    hconjsmooth.contDiffOn
  have hconjne : ∀ ζ ∈ {z : ℂ | z ≠ 0}, (fun z : ℂ => starRingEnd ℂ z) ζ ≠ 0 := by
    intro ζ hζ
    simpa using hζ
  have hDZid : ∀ z : ℂ, DZ (fun w : ℂ => w) z = 1 ∧ DZbar (fun w : ℂ => w) z = 0 := by
    intro z
    have h : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id
    refine ⟨?_, ?_⟩ <;>
      simp only [DZ, DZbar, h, ContinuousLinearMap.id_apply] <;>
      rw [Complex.I_mul_I] <;> ring
  have hDZconj : ∀ z : ℂ, DZ (fun w : ℂ => starRingEnd ℂ w) z = 0 ∧
      DZbar (fun w : ℂ => starRingEnd ℂ w) z = 1 := by
    intro z
    have h := WirtingerConjRule (fun w : ℂ => w) z differentiableAt_id
    exact ⟨by rw [h.1, (hDZid z).2, map_zero], by rw [h.2, (hDZid z).1, map_one]⟩
  have hDZadd : ∀ (f g : ℂ → ℂ) (z : ℂ), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z →
      DZ (fun w => f w + g w) z = DZ f z + DZ g z ∧
      DZbar (fun w => f w + g w) z = DZbar f z + DZbar g z := by
    intro f g z hf hg
    have h : fderiv ℝ (fun w => f w + g w) z = fderiv ℝ f z + fderiv ℝ g z :=
      (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
    refine ⟨?_, ?_⟩ <;> simp only [DZ, DZbar, h, add_apply] <;> ring
  have hDZcmul : ∀ (c : ℂ) (f : ℂ → ℂ) (z : ℂ), DifferentiableAt ℝ f z →
      DZ (fun w => c * f w) z = c * DZ f z ∧
      DZbar (fun w => c * f w) z = c * DZbar f z := by
    intro c f z hf
    have h : fderiv ℝ (fun w => c * f w) z = c • fderiv ℝ f z := fderiv_const_mul hf c
    refine ⟨?_, ?_⟩ <;> simp only [DZ, DZbar, h, smul_apply, smul_eq_mul] <;> ring
  have hDZ3 : ∀ (f g h : ℂ → ℂ) (z : ℂ), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z →
      DifferentiableAt ℝ h z →
      DZ (fun w => f w * g w * h w) z
        = (DZ f z * g z + f z * DZ g z) * h z + f z * g z * DZ h z ∧
      DZbar (fun w => f w * g w * h w) z
        = (DZbar f z * g z + f z * DZbar g z) * h z + f z * g z * DZbar h z := by
    intro f g h z hf hg hh
    have h1 := WirtingerProductRule (fun w => f w * g w) h z (hf.mul hg) hh
    have h2 := WirtingerProductRule f g z hf hg
    exact ⟨by rw [h1.1, h2.1], by rw [h1.2, h2.2]⟩
  have hDZpowneg : ∀ ξ : ℂ, ξ ≠ 0 →
      DZ (fun z : ℂ => z ^ (-(n : ℤ))) ξ = (-(n : ℂ)) * ξ ^ (-(n : ℤ) - 1) ∧
      DZbar (fun z : ℂ => z ^ (-(n : ℤ))) ξ = 0 := by
    intro ξ hξ
    have h := WirtingerPowerRule (fun z : ℂ => z) {z : ℂ | z ≠ 0} hΩ0 hidC hidne
      (-(n : ℤ)) ξ hξ
    refine ⟨?_, ?_⟩
    · rw [h.1, (hDZid ξ).1, mul_one]
      push_cast
      ring
    · rw [h.2, (hDZid ξ).2, mul_zero]
  have hHsmooth : ∀ ξ : ℂ, ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ (-(n : ℤ))) ξ := by
    intro ξ hξ
    have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ n) ξ := (contDiff_id.pow n).contDiffAt
    have h := hb.inv (by simpa using pow_ne_zero n hξ)
    simpa [zpow_neg, zpow_natCast, Pi.inv_def] using h
  have hHd : ∀ ξ : ℂ, ξ ≠ 0 →
      DifferentiableAt ℝ (fun z : ℂ => z ^ (-(n : ℤ))) ξ :=
    fun ξ hξ => (hHsmooth ξ hξ).differentiableAt hone
  have hFsmooth : ∀ ζ : ℂ, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => A (k : ℤ) * z ^ k
        + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ z) ^ k) ζ := by
    intro ζ
    refine ContDiffAt.add ?_ ?_
    · exact contDiffAt_const.mul ((contDiff_id.pow k).contDiffAt)
    · exact contDiffAt_const.mul ((hconjsmooth.pow k).contDiffAt)
  have hGsmooth : ∀ ζ : ℂ, ζ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) ζ :=
    fun ζ hζ => (WirtingerModulusPowerRule (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) ζ hζ).1
  have hFd : ∀ ζ : ℂ, DifferentiableAt ℝ
      (fun z : ℂ => A (k : ℤ) * z ^ k
        + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ z) ^ k) ζ := fun ζ => (hFsmooth ζ).differentiableAt hone
  have hGd : ∀ ζ : ℂ, ζ ≠ 0 → DifferentiableAt ℝ
      (fun z : ℂ => ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) ζ :=
    fun ζ hζ => (hGsmooth ζ hζ).differentiableAt hone
  have hDZpowk : ∀ ζ : ℂ, ζ ≠ 0 →
      DZ (fun z : ℂ => z ^ k) ζ = (k : ℂ) * ζ ^ ((k : ℤ) - 1) ∧
      DZbar (fun z : ℂ => z ^ k) ζ = 0 := by
    intro ζ hζ
    have hfun : (fun z : ℂ => z ^ ((k : ℕ) : ℤ)) = (fun z : ℂ => z ^ k) := by
      funext z; rw [zpow_natCast]
    have h := WirtingerPowerRule (fun z : ℂ => z) {z : ℂ | z ≠ 0} hΩ0 hidC hidne
      ((k : ℕ) : ℤ) ζ hζ
    rw [hfun] at h
    refine ⟨?_, ?_⟩
    · rw [h.1, (hDZid ζ).1, mul_one]
      push_cast
      ring
    · rw [h.2, (hDZid ζ).2, mul_zero]
  have hDZpowconjk : ∀ ζ : ℂ, ζ ≠ 0 →
      DZ (fun z : ℂ => (starRingEnd ℂ z) ^ k) ζ = 0 ∧
      DZbar (fun z : ℂ => (starRingEnd ℂ z) ^ k) ζ
        = (k : ℂ) * (starRingEnd ℂ ζ) ^ ((k : ℤ) - 1) := by
    intro ζ hζ
    have hfun : (fun z : ℂ => (starRingEnd ℂ z) ^ ((k : ℕ) : ℤ))
        = (fun z : ℂ => (starRingEnd ℂ z) ^ k) := by
      funext z; rw [zpow_natCast]
    have h := WirtingerPowerRule (fun z : ℂ => starRingEnd ℂ z) {z : ℂ | z ≠ 0} hΩ0 hconjC
      hconjne ((k : ℕ) : ℤ) ζ hζ
    rw [hfun] at h
    refine ⟨?_, ?_⟩
    · rw [h.1, (hDZconj ζ).1, mul_zero]
    · rw [h.2, (hDZconj ζ).2, mul_one]
      push_cast
      ring
  have hDZF : ∀ ζ : ℂ, ζ ≠ 0 →
      DZ (fun z : ℂ => A (k : ℤ) * z ^ k
          + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ z) ^ k) ζ
        = (k : ℂ) * A (k : ℤ) * ζ ^ ((k : ℤ) - 1) ∧
      DZbar (fun z : ℂ => A (k : ℤ) * z ^ k
          + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ z) ^ k) ζ
        = (k : ℂ) * ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
            * (starRingEnd ℂ ζ) ^ ((k : ℤ) - 1) := by
    intro ζ hζ
    have hd1 : DifferentiableAt ℝ (fun z : ℂ => A (k : ℤ) * z ^ k) ζ :=
      (differentiableAt_id.pow k).const_mul _
    have hdc : DifferentiableAt ℝ (fun z : ℂ => (starRingEnd ℂ z) ^ k) ζ :=
      (Complex.conjCLE.differentiableAt).pow k
    have hd2 : DifferentiableAt ℝ (fun z : ℂ =>
        ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)) * (starRingEnd ℂ z) ^ k) ζ :=
      hdc.const_mul _
    have ha := hDZadd _ _ ζ hd1 hd2
    have hc1 := hDZcmul (A (k : ℤ)) (fun z : ℂ => z ^ k) ζ (differentiableAt_id.pow k)
    have hc2 := hDZcmul (((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)))
      (fun z : ℂ => (starRingEnd ℂ z) ^ k) ζ hdc
    have hre : (fun z : ℂ => ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ z) ^ k)
        = (fun z : ℂ => (((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)))
          * (starRingEnd ℂ z) ^ k) := by funext z; ring
    refine ⟨?_, ?_⟩
    · rw [ha.1, hre] at *
      rw [hc1.1, hc2.1, (hDZpowk ζ hζ).1, (hDZpowconjk ζ hζ).1]
      ring
    · rw [ha.2, hre] at *
      rw [hc1.2, hc2.2, (hDZpowk ζ hζ).2, (hDZpowconjk ζ hζ).2]
      ring
  have hTfun : Thm2Term n p A k = fun z : ℂ =>
      (A (k : ℤ) * z ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
          * (starRingEnd ℂ z) ^ k)
        * ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ) * z ^ (-(n : ℤ)) := rfl
  have hyne : starRingEnd ℂ ξ ≠ 0 := by simpa using hξ
  have hz1 : ξ ^ ((k : ℤ) - 1) = ξ ^ k / ξ := by
    rw [zpow_sub₀ hξ, zpow_natCast, zpow_one]
  have hz1' : (starRingEnd ℂ ξ) ^ ((k : ℤ) - 1)
      = (starRingEnd ℂ ξ) ^ k / starRingEnd ℂ ξ := by
    rw [zpow_sub₀ hyne, zpow_natCast, zpow_one]
  have hz2 : ξ ^ (-(n : ℤ) - 1) = ξ ^ (-(n : ℤ)) / ξ := by
    rw [zpow_sub₀ hξ, zpow_one]
  have hW := WirtingerModulusPowerRule (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) ξ hξ
  refine ⟨?_, ?_⟩
  · calc DZ (Thm2Term n p A k) ξ
        = (DZ (fun z : ℂ => A (k : ℤ) * z ^ k
                + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                    * (starRingEnd ℂ z) ^ k) ξ
              * ((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
            + (A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                * (starRingEnd ℂ ξ) ^ k)
              * DZ (fun z : ℂ =>
                  ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) ξ)
            * ξ ^ (-(n : ℤ))
          + (A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ ξ) ^ k)
            * ((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
            * DZ (fun z : ℂ => z ^ (-(n : ℤ))) ξ := by
          rw [hTfun]
          exact (hDZ3 _ _ _ ξ (hFd ξ) (hGd ξ hξ) (hHd ξ hξ)).1
      _ = _ := by
          rw [(hDZF ξ hξ).1, hW.2.1, (hDZpowneg ξ hξ).1, hz1, hz2]
          push_cast
          field_simp
          ring
  · calc DZbar (Thm2Term n p A k) ξ
        = (DZbar (fun z : ℂ => A (k : ℤ) * z ^ k
                + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                    * (starRingEnd ℂ z) ^ k) ξ
              * ((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
            + (A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                * (starRingEnd ℂ ξ) ^ k)
              * DZbar (fun z : ℂ =>
                  ((‖z‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)) ξ)
            * ξ ^ (-(n : ℤ))
          + (A (k : ℤ) * ξ ^ k + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
              * (starRingEnd ℂ ξ) ^ k)
            * ((‖ξ‖ ^ (LambdaCoef n k p + (n : ℝ) - (k : ℝ)) : ℝ) : ℂ)
            * DZbar (fun z : ℂ => z ^ (-(n : ℤ))) ξ := by
          rw [hTfun]
          exact (hDZ3 _ _ _ ξ (hFd ξ) (hGd ξ hξ) (hHd ξ hξ)).2
      _ = _ := by
          rw [(hDZF ξ hξ).2, hW.2.2, (hDZpowneg ξ hξ).2, hz1']
          push_cast
          field_simp
          ring
