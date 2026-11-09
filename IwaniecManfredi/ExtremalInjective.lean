import IwaniecManfredi.ExtremalPolarForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import IwaniecManfredi.ExtremalEpsBound

/-- The extremal function (54) of Section 7 is a homeomorphism of the plane
onto itself.  This is the paper's assertion at `paper.tex:586` that "in this
case `H` is a quasiconformal homeomorphism on the whole plane", in the only
form Section 7 uses: that `H` has a continuous inverse `f` defined on all of
`ℂ`, which is what (55) presupposes.  The mechanism is `|ε| < 1/3` *strictly*:
writing `G(θ) = e^{iθ}(1 + ε e^{-4iθ})`, the derivative of `arg G` is
`Re((1-3w)/(1+w)) = (1 - 2 Re w - 3|w|²)/|1+w|²` at `w = ε e^{-4iθ}`, which is
bounded below by `(1-3|ε|)(1+|ε|)/|1+w|² > 0`; so `arg G` increases strictly,
and by exactly `2π` over a period.  No degree theory is involved. -/
theorem ExtremalInjective (p : ℝ) (hp : 1 < p) :
    Continuous (ExtremalH p) ∧ Function.Bijective (ExtremalH p) ∧
      ∃ g : ℂ → ℂ, Continuous g ∧
        (∀ ξ : ℂ, g (ExtremalH p ξ) = ξ) ∧ (∀ z : ℂ, ExtremalH p (g z) = z) := by
  -- ## Step 0: the two constants
  have hd : 0 < DExp p := by
    unfold DExp
    have h1 : 0 < 1 / (p - 1) := by positivity
    have h2 : 0 ≤ Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2) := Real.sqrt_nonneg _
    linarith
  obtain ⟨-, hepsb, -⟩ := ExtremalEpsBound p hp
  obtain ⟨eps, hepsdef⟩ : ∃ x : ℝ, x = EpsCoef 1 2 p := ⟨_, rfl⟩
  rw [← hepsdef] at hepsb
  obtain ⟨a, hadef⟩ : ∃ x : ℝ, x = 1 / DExp p := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [hadef]; positivity
  have he0 : (0 : ℝ) ≤ |eps| := abs_nonneg eps
  have he1 : (0 : ℝ) < 1 - |eps| := by linarith
  -- ## Step 1 (4): `G θ = e^{iθ}(1 + w θ)` with `w θ = ε e^{-4iθ}`
  obtain ⟨w, hwdef⟩ : ∃ f : ℝ → ℂ,
      f = fun θ : ℝ => (eps : ℂ) * Complex.exp (-(4 * (θ : ℂ)) * Complex.I) := ⟨_, rfl⟩
  have hwnorm : ∀ θ : ℝ, ‖w θ‖ = |eps| := by
    intro θ
    rw [hwdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show -(4 * (θ : ℂ)) * Complex.I = ((-(4 * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hGsplit : ∀ θ : ℝ,
      Complex.exp ((θ : ℂ) * Complex.I) + (eps : ℂ) * Complex.exp (-(3 * (θ : ℂ)) * Complex.I)
        = Complex.exp ((θ : ℂ) * Complex.I) * (1 + w θ) := by
    intro θ
    rw [hwdef]
    simp only
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (Complex.exp ((θ : ℂ) * Complex.I)) (eps : ℂ),
      mul_assoc, ← Complex.exp_add]
    congr 2
    ring_nf
  -- ## Step 3: the lift `Θ` through `Complex.log`, and `1 + w θ` in the slit plane
  have hre : ∀ θ : ℝ, 1 - |eps| ≤ (1 + w θ).re := by
    intro θ
    have h1 : |(w θ).re| ≤ ‖w θ‖ := Complex.abs_re_le_norm _
    rw [hwnorm θ] at h1
    simp only [Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp h1).1]
  have hposre : ∀ θ : ℝ, 0 < (1 + w θ).re := fun θ => by linarith [hre θ]
  have hslit : ∀ θ : ℝ, (1 + w θ) ∈ Complex.slitPlane := fun θ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (hposre θ))
  have hwne : ∀ θ : ℝ, (1 + w θ) ≠ 0 := by
    intro θ h
    have := hposre θ
    rw [h] at this
    simp at this
  have hwd : ∀ θ : ℝ, HasDerivAt w ((-4 * Complex.I) * w θ) θ := by
    intro θ
    have hc : HasDerivAt (fun s : ℝ => (-(4 * (s : ℂ)) * Complex.I))
        ((-4 : ℂ) * Complex.I) θ := by
      have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) 1 θ := Complex.ofRealCLM.hasDerivAt
      simpa using ((h1.const_mul (-4 : ℂ)).mul_const Complex.I)
    have h3 := (hc.cexp).const_mul (eps : ℂ)
    have hval : (eps : ℂ) * (Complex.exp (-(4 * (θ : ℂ)) * Complex.I) * ((-4 : ℂ) * Complex.I))
        = (-4 * Complex.I) * w θ := by rw [hwdef]; ring
    -- the derivative VALUE is written out, so `rw [hwdef]` touches only the
    -- function position; then transport the value
    have h4 : HasDerivAt w
        ((eps : ℂ) * (Complex.exp (-(4 * (θ : ℂ)) * Complex.I) * ((-4 : ℂ) * Complex.I))) θ := by
      rw [hwdef]; exact h3
    rw [hval] at h4
    exact h4
  -- `HasDerivAt.im`, which Mathlib does not have: go through `HasFDerivAt` with the
  -- derivative written as `imCLM ∘ smulRight 1 f'`, which dodges the ℝ-module
  -- instance diamond that `comp_hasDerivAt` runs into.
  have hIm : ∀ (f : ℝ → ℂ) (f' : ℂ) (t : ℝ), HasDerivAt f f' t →
      HasDerivAt (fun s => (f s).im) f'.im t := by
    intro f f' t h
    have h2 : HasFDerivAt (fun s : ℝ => (f s).im)
        (Complex.imCLM.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f')) t :=
      Complex.imCLM.hasFDerivAt.comp t h.hasFDerivAt
    simpa using h2.hasDerivAt
  obtain ⟨Θ, hΘdef⟩ : ∃ f : ℝ → ℝ,
      f = fun θ : ℝ => θ + (Complex.log (1 + w θ)).im := ⟨_, rfl⟩
  obtain ⟨mu, hmudef⟩ : ∃ x : ℝ, x = (1 - 3 * |eps|) / (1 + |eps|) := ⟨_, rfl⟩
  have hmupos : 0 < mu := by
    rw [hmudef]
    apply div_pos (by linarith) (by linarith)
  have hΘd : ∀ θ : ℝ, HasDerivAt Θ
      (1 + ((1 + w θ)⁻¹ * ((-4 * Complex.I) * w θ)).im) θ := by
    intro θ
    have hlog0 := (Complex.hasDerivAt_log (hslit θ)).comp θ ((hwd θ).const_add 1)
    have hlog : HasDerivAt (fun s : ℝ => Complex.log (1 + w s))
        ((1 + w θ)⁻¹ * ((-4 * Complex.I) * w θ)) θ := hlog0
    have him := hIm _ _ θ hlog
    have hid : HasDerivAt (fun s : ℝ => s) 1 θ := hasDerivAt_id θ
    have := hid.add him
    rw [hΘdef]
    exact this
  -- ## (9): the `μ > 0` lower bound on `Θ'`
  have hmubound : ∀ θ : ℝ, mu ≤ 1 + ((1 + w θ)⁻¹ * ((-4 * Complex.I) * w θ)).im := by
    intro θ
    obtain ⟨c, hcdef⟩ : ∃ y : ℂ, y = w θ := ⟨_, rfl⟩
    rw [← hcdef, hmudef]
    have hc : ‖c‖ = |eps| := by rw [hcdef]; exact hwnorm θ
    have hab : |eps| ^ 2 = eps ^ 2 := sq_abs eps
    have hsq : c.re ^ 2 + c.im ^ 2 = eps ^ 2 := by
      have h : ‖c‖ ^ 2 = |eps| ^ 2 := by rw [hc]
      rw [Complex.sq_norm, Complex.normSq_apply] at h
      nlinarith [h, hab]
    have hreb := abs_le.mp (by rw [← hc]; exact Complex.abs_re_le_norm c : |c.re| ≤ |eps|)
    have hApos : (0 : ℝ) < 1 + 2 * c.re + eps ^ 2 := by
      nlinarith [hreb.1, hepsb, hab, he0]
    have hcre : (0 : ℝ) < (1 + c).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith [hreb.1]
    have h1c : (1 + c) ≠ 0 := by
      intro h; rw [h] at hcre; simp at hcre
    obtain ⟨q, hqdef⟩ : ∃ y : ℂ, y = (1 + c)⁻¹ * ((-4 * Complex.I) * c) := ⟨_, rfl⟩
    rw [← hqdef]
    have hprod : q * (1 + c) = (-4 : ℂ) * Complex.I * c := by
      rw [hqdef]; field_simp
    have e1 : q.re * (1 + c.re) - q.im * c.im = 4 * c.im := by
      have := congrArg Complex.re hprod
      simpa [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im] using this
    have e2 : q.re * c.im + q.im * (1 + c.re) = -4 * c.re := by
      have := congrArg Complex.im hprod
      simpa [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im] using this
    have hq : (1 + 2 * c.re + eps ^ 2) * q.im = -4 * (c.re + eps ^ 2) := by
      have h : ((1 + c.re) ^ 2 + c.im ^ 2) * q.im = -4 * (c.re + (c.re ^ 2 + c.im ^ 2)) := by
        linear_combination (1 + c.re) * e2 - c.im * e1
      rw [hsq] at h
      linear_combination h - q.im * hsq
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + |eps|)]
    nlinarith [hq, hApos, mul_nonneg (by linarith [hreb.2] : (0 : ℝ) ≤ |eps| - c.re)
      (by linarith : (0 : ℝ) ≤ 1 - |eps|), hab]
  -- ## Step 3 tail: `Θ θ₂ - Θ θ₁ ≥ μ(θ₂ - θ₁)`, via monotonicity of `Θ - μ·id`
  obtain ⟨Φ, hΦdef⟩ : ∃ f : ℝ → ℝ, f = fun θ : ℝ => Θ θ - mu * θ := ⟨_, rfl⟩
  have hΦd : ∀ θ : ℝ, HasDerivAt Φ
      ((1 + ((1 + w θ)⁻¹ * ((-4 * Complex.I) * w θ)).im) - mu * 1) θ := by
    intro θ
    have h := (hΘd θ).sub ((hasDerivAt_id θ).const_mul mu)
    rw [hΦdef]
    exact h
  have hΦmono : Monotone Φ := by
    refine monotone_of_deriv_nonneg (fun θ => (hΦd θ).differentiableAt) (fun θ => ?_)
    rw [(hΦd θ).deriv]
    linarith [hmubound θ]
  have hlin : ∀ θ₁ θ₂ : ℝ, θ₁ ≤ θ₂ → mu * (θ₂ - θ₁) ≤ Θ θ₂ - Θ θ₁ := by
    intro θ₁ θ₂ h
    have h2 := hΦmono h
    rw [hΦdef] at h2
    simp only at h2
    linarith
  have hΘmono : StrictMono Θ := by
    intro θ₁ θ₂ h
    have h2 := hlin θ₁ θ₂ h.le
    nlinarith [hmupos, sub_pos.mpr h]
  have hΘcont : Continuous Θ :=
    continuous_iff_continuousAt.mpr (fun θ => (hΘd θ).continuousAt)
  -- ## Step 4 (10): `w` is `2π`-periodic, so `Θ(θ + 2π) = Θ(θ) + 2π`
  have hwper : ∀ θ : ℝ, w (θ + 2 * Real.pi) = w θ := by
    intro θ
    rw [hwdef]
    simp only
    have hsplit : -(4 * ((θ + 2 * Real.pi : ℝ) : ℂ)) * Complex.I
        = -(4 * (θ : ℂ)) * Complex.I + (-4 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hΘper : ∀ θ : ℝ, Θ (θ + 2 * Real.pi) = Θ θ + 2 * Real.pi := by
    intro θ
    rw [hΘdef]
    simp only
    rw [hwper θ]
    ring
  -- ## Step 4: `Θ` is onto `ℝ`, by the linear bound and the intermediate value theorem
  have hΘsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨t, htdef⟩ : ∃ x : ℝ, x = (y - Θ 0) / mu := ⟨_, rfl⟩
    have hmt : mu * t = y - Θ 0 := by
      rw [htdef]; field_simp
    obtain ⟨lo, hlodef⟩ : ∃ x : ℝ, x = min 0 t := ⟨_, rfl⟩
    obtain ⟨hi, hhidef⟩ : ∃ x : ℝ, x = max 0 t := ⟨_, rfl⟩
    have hle : lo ≤ hi := by
      rw [hlodef, hhidef]; exact le_trans (min_le_left _ _) (le_max_left _ _)
    have hlo0 : lo ≤ 0 := by rw [hlodef]; exact min_le_left _ _
    have hhi0 : 0 ≤ hi := by rw [hhidef]; exact le_max_left _ _
    have hLlo : Θ lo ≤ y := by
      have h2 := hlin lo 0 hlo0
      rcases le_or_gt t 0 with ht | ht
      · have hlt : lo = t := by rw [hlodef]; exact min_eq_right ht
        rw [hlt] at h2 ⊢
        linarith [hmt]
      · have hl0 : lo = 0 := by rw [hlodef]; exact min_eq_left ht.le
        rw [hl0] at h2 ⊢
        nlinarith [hmt, hmupos, ht]
    have hLhi : y ≤ Θ hi := by
      have h2 := hlin 0 hi hhi0
      rcases le_or_gt t 0 with ht | ht
      · have hh0 : hi = 0 := by rw [hhidef]; exact max_eq_left ht
        rw [hh0] at h2 ⊢
        nlinarith [hmt, hmupos, ht]
      · have hht : hi = t := by rw [hhidef]; exact max_eq_right ht.le
        rw [hht] at h2 ⊢
        linarith [hmt]
    have hsub := intermediate_value_Icc hle (hΘcont.continuousOn)
    obtain ⟨θ, -, hθ⟩ := hsub (Set.mem_Icc.mpr ⟨hLlo, hLhi⟩)
    exact ⟨θ, hθ⟩
  -- ## Step 1 (6): two-sided control of `‖H ξ‖`, read off the formula directly
  have hH0 : ExtremalH p 0 = 0 := by unfold ExtremalH; simp
  have hunit : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ / ((‖ξ‖ : ℝ) : ℂ)‖ = 1 := by
    intro ξ hξ
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg ξ)]
    exact div_self (norm_ne_zero_iff.mpr hξ)
  have hcube : ∀ ξ : ℂ, ξ ≠ 0 →
      ‖(eps : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3)‖ = |eps| := by
    intro ξ hξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg ξ),
      div_self (pow_ne_zero 3 (norm_ne_zero_iff.mpr hξ)), mul_one]
  have hHbound : ∀ ξ : ℂ, ξ ≠ 0 →
      (1 - |eps|) * ‖ξ‖ ^ a ≤ ‖ExtremalH p ξ‖ ∧ ‖ExtremalH p ξ‖ ≤ (1 + |eps|) * ‖ξ‖ ^ a := by
    intro ξ hξ
    have hfac : ‖ExtremalH p ξ‖
        = ‖ξ / ((‖ξ‖ : ℝ) : ℂ) + (eps : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3)‖ * ‖ξ‖ ^ a := by
      unfold ExtremalH
      rw [← hepsdef, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _), ← hadef]
    have hup : ‖ξ / ((‖ξ‖ : ℝ) : ℂ) + (eps : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3)‖
        ≤ 1 + |eps| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [hunit ξ hξ, hcube ξ hξ]
    have hdn : 1 - |eps| ≤ ‖ξ / ((‖ξ‖ : ℝ) : ℂ) + (eps : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3)‖ := by
      have h := norm_sub_norm_le (ξ / ((‖ξ‖ : ℝ) : ℂ))
        (-((eps : ℂ) * (((‖ξ‖ : ℝ) : ℂ) ^ 3 / ξ ^ 3)))
      rw [hunit ξ hξ, norm_neg, hcube ξ hξ, sub_neg_eq_add] at h
      exact h
    have hrp : (0 : ℝ) ≤ ‖ξ‖ ^ a := Real.rpow_nonneg (norm_nonneg ξ) _
    rw [hfac]
    exact ⟨mul_le_mul_of_nonneg_right hdn hrp, mul_le_mul_of_nonneg_right hup hrp⟩
  -- ## Step 2: continuity of `H`
  have hcontne : ∀ ξ : ℂ, ξ ≠ 0 → ContinuousAt (ExtremalH p) ξ := by
    intro ξ hξ
    have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hnc : ContinuousAt (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)) ξ :=
      (Complex.continuous_ofReal.continuousAt).comp (continuous_norm.continuousAt)
    have h1 : ContinuousAt (fun y : ℂ => y / ((‖y‖ : ℝ) : ℂ)) ξ :=
      continuousAt_id.div hnc (by simpa using hn)
    have h2 : ContinuousAt (fun y : ℂ => (eps : ℂ) * (((‖y‖ : ℝ) : ℂ) ^ 3 / y ^ 3)) ξ :=
      continuousAt_const.mul ((hnc.pow 3).div (continuousAt_id.pow 3)
        (pow_ne_zero 3 hξ))
    have h3 : ContinuousAt (fun y : ℂ => ((‖y‖ ^ a : ℝ) : ℂ)) ξ := by
      refine (Complex.continuous_ofReal.continuousAt).comp ?_
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hn)).comp
        (continuous_norm.continuousAt)
    have : ContinuousAt (fun y : ℂ =>
        (y / ((‖y‖ : ℝ) : ℂ) + (eps : ℂ) * (((‖y‖ : ℝ) : ℂ) ^ 3 / y ^ 3))
          * ((‖y‖ ^ a : ℝ) : ℂ)) ξ := (h1.add h2).mul h3
    unfold ExtremalH
    rw [← hepsdef, ← hadef]
    exact this
  have hcont0 : ContinuousAt (ExtremalH p) 0 := by
    have hzero : (0 : ℝ) ^ a = 0 := Real.zero_rpow hapos.ne'
    have hall : ∀ ξ : ℂ, ‖ExtremalH p ξ‖ ≤ (1 + |eps|) * ‖ξ‖ ^ a := by
      intro ξ
      rcases eq_or_ne ξ 0 with h | h
      · subst h; rw [hH0]; simp [hzero]
      · exact (hHbound ξ h).2
    have hg : Filter.Tendsto (fun ξ : ℂ => (1 + |eps|) * ‖ξ‖ ^ a) (nhds 0) (nhds 0) := by
      have hn : Filter.Tendsto (fun ξ : ℂ => ‖ξ‖) (nhds 0) (nhds 0) := by
        have h := (continuous_norm (E := ℂ)).continuousAt (x := (0 : ℂ))
        rw [ContinuousAt, norm_zero] at h
        exact h
      have hr : Filter.Tendsto (fun t : ℝ => t ^ a) (nhds 0) (nhds 0) := by
        have h := Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr hapos.le)
        rw [ContinuousAt, hzero] at h
        exact h
      have := (hr.comp hn).const_mul (1 + |eps|)
      simpa using this
    have : Filter.Tendsto (ExtremalH p) (nhds 0) (nhds 0) :=
      squeeze_zero_norm (fun ξ => hall ξ) hg
    rw [ContinuousAt, hH0]
    exact this
  have hHcont : Continuous (ExtremalH p) := by
    refine continuous_iff_continuousAt.mpr (fun ξ => ?_)
    rcases eq_or_ne ξ 0 with h | h
    · subst h; exact hcont0
    · exact hcontne ξ h
  -- ## (7): the polar form of `G`, through `Complex.log_im = arg`
  have hpolar : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) * (1 + w θ)
      = ((‖1 + w θ‖ : ℝ) : ℂ) * Complex.exp (((Θ θ : ℝ) : ℂ) * Complex.I) := by
    intro θ
    have harg : (Complex.log (1 + w θ)).im = Complex.arg (1 + w θ) := Complex.log_im _
    have hsplit : ((Θ θ : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + ((Complex.arg (1 + w θ) : ℝ) : ℂ) * Complex.I := by
      rw [hΘdef]
      simp only
      rw [harg]
      push_cast
      ring
    rw [hsplit, Complex.exp_add,
      show ((‖1 + w θ‖ : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
            * Complex.exp (((Complex.arg (1 + w θ) : ℝ) : ℂ) * Complex.I))
          = Complex.exp ((θ : ℂ) * Complex.I) * (((‖1 + w θ‖ : ℝ) : ℂ)
            * Complex.exp (((Complex.arg (1 + w θ) : ℝ) : ℂ) * Complex.I)) by ring,
      Complex.norm_mul_exp_arg_mul_I]
  -- ## (3) + (7): `H` in polar coordinates
  have hHpolar : ∀ ξ : ℂ, ξ ≠ 0 →
      ExtremalH p ξ = ((‖ξ‖ ^ a * ‖1 + w (Complex.arg ξ)‖ : ℝ) : ℂ)
        * Complex.exp (((Θ (Complex.arg ξ) : ℝ) : ℂ) * Complex.I) := by
    intro ξ hξ
    have hpf := (ExtremalPolarForm p hp).1 ‖ξ‖ (norm_pos_iff.mpr hξ) (Complex.arg ξ)
    rw [Complex.norm_mul_exp_arg_mul_I ξ, ← hepsdef, hGsplit (Complex.arg ξ),
      hpolar (Complex.arg ξ), ← hadef] at hpf
    rw [hpf]
    push_cast
    ring
  -- the modulus factor is positive
  have hMpos : ∀ ξ : ℂ, ξ ≠ 0 → 0 < ‖ξ‖ ^ a * ‖1 + w (Complex.arg ξ)‖ := by
    intro ξ hξ
    have h1 : 0 < ‖ξ‖ ^ a := Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) _
    have h2 : 0 < ‖1 + w (Complex.arg ξ)‖ := by
      have := hre (Complex.arg ξ)
      have h3 : 0 < (1 + w (Complex.arg ξ)).re := by linarith
      refine norm_pos_iff.mpr (fun hc => ?_)
      rw [hc] at h3; simp at h3
    positivity
  -- `t ↦ t ^ a` is injective on the nonnegatives
  have hrpowinj : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s ^ a = t ^ a → s = t := by
    intro s t hs ht h
    have h1 : (s ^ a) ^ (1 / a) = (t ^ a) ^ (1 / a) := by rw [h]
    rwa [← Real.rpow_mul hs, ← Real.rpow_mul ht, mul_one_div, div_self hapos.ne',
      Real.rpow_one, Real.rpow_one] at h1
  -- ## Steps 5 and 6: `H` is a bijection of `ℂ`.
  -- Injectivity: for `ξ ≠ 0` write `ξ = r e^{iθ}`, use (3) and (7) to read off
  -- modulus and unit vector, then `Complex.exp_eq_exp_iff_exists_int` plus
  -- `hΘper` and `hΘmono` to force `θ₁ = θ₂ + 2πk`, hence `r₁ = r₂`.
  -- Surjectivity: `hΘsurj` supplies the angle and `r = s ^ DExp p` the modulus.
  have hbij : Function.Bijective (ExtremalH p) := by
    have hnz : ∀ ξ : ℂ, ξ ≠ 0 → ExtremalH p ξ ≠ 0 := by
      intro ξ hξ hc
      have hM := hMpos ξ hξ
      have hn := congrArg norm (hHpolar ξ hξ)
      rw [hc, norm_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM.le,
        Complex.norm_exp_ofReal_mul_I, mul_one] at hn
      exact absurd hn.symm (ne_of_gt hM)
    refine ⟨?_, ?_⟩
    · -- ## Step 5: injectivity
      intro ξ₁ ξ₂ hEq
      rcases eq_or_ne ξ₁ 0 with h1 | h1
      · rcases eq_or_ne ξ₂ 0 with h2 | h2
        · rw [h1, h2]
        · exfalso
          rw [h1, hH0] at hEq
          exact hnz ξ₂ h2 hEq.symm
      · rcases eq_or_ne ξ₂ 0 with h2 | h2
        · exfalso
          rw [h2, hH0] at hEq
          exact hnz ξ₁ h1 hEq
        · -- both nonzero: compare moduli, then unit vectors
          have hM1 := hMpos ξ₁ h1
          have hM2 := hMpos ξ₂ h2
          have hE := hEq
          rw [hHpolar ξ₁ h1, hHpolar ξ₂ h2] at hE
          have hmod : ‖ξ₁‖ ^ a * ‖1 + w (Complex.arg ξ₁)‖
              = ‖ξ₂‖ ^ a * ‖1 + w (Complex.arg ξ₂)‖ := by
            have hn := congrArg norm hE
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg hM1.le, Real.norm_of_nonneg hM2.le,
              Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
              mul_one, mul_one] at hn
            exact hn
          have hexp : Complex.exp (((Θ (Complex.arg ξ₁) : ℝ) : ℂ) * Complex.I)
              = Complex.exp (((Θ (Complex.arg ξ₂) : ℝ) : ℂ) * Complex.I) := by
            have hne : ((‖ξ₁‖ ^ a * ‖1 + w (Complex.arg ξ₁)‖ : ℝ) : ℂ) ≠ 0 := by
              simpa using ne_of_gt hM1
            rw [hmod] at hE
            exact mul_left_cancel₀ (by rw [← hmod]; exact hne) hE
          obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
          have hmul : (((Θ (Complex.arg ξ₁) : ℝ) : ℂ) - ((Θ (Complex.arg ξ₂) : ℝ) : ℂ)
              - (k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I = 0 := by
            linear_combination hk
          have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
          have hreal : Θ (Complex.arg ξ₁) - Θ (Complex.arg ξ₂)
              - (k : ℝ) * (2 * Real.pi) = 0 := by
            have := congrArg Complex.re h0
            simpa using this
          -- the argument bounds force `k = 0`
          have hb1 := Complex.neg_pi_lt_arg ξ₁
          have hb2 := Complex.arg_le_pi ξ₁
          have hb3 := Complex.neg_pi_lt_arg ξ₂
          have hb4 := Complex.arg_le_pi ξ₂
          have hpi := Real.pi_pos
          have hk0 : k = 0 := by
            rcases lt_trichotomy k 0 with hlt | heq | hgt
            · exfalso
              have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_of_lt_add_one (by omega)
              have hper : Θ (Complex.arg ξ₂ - 2 * Real.pi)
                  = Θ (Complex.arg ξ₂) - 2 * Real.pi := by
                have h := hΘper (Complex.arg ξ₂ - 2 * Real.pi)
                rw [sub_add_cancel] at h
                linarith
              have hle : Θ (Complex.arg ξ₁) ≤ Θ (Complex.arg ξ₂ - 2 * Real.pi) := by
                rw [hper]; nlinarith
              have := (hΘmono.le_iff_le).mp hle
              linarith
            · exact heq
            · exfalso
              have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
              have hper := hΘper (Complex.arg ξ₂)
              have hle : Θ (Complex.arg ξ₂ + 2 * Real.pi) ≤ Θ (Complex.arg ξ₁) := by
                rw [hper]; nlinarith
              have := (hΘmono.le_iff_le).mp hle
              linarith
          rw [hk0] at hreal
          push_cast at hreal
          have hargeq : Complex.arg ξ₁ = Complex.arg ξ₂ :=
            hΘmono.injective (by linarith)
          -- equal arguments, then equal moduli
          rw [hargeq] at hmod
          have hKp : 0 < ‖1 + w (Complex.arg ξ₂)‖ := by
            have h3 : 0 < (1 + w (Complex.arg ξ₂)).re := by linarith [hre (Complex.arg ξ₂)]
            refine norm_pos_iff.mpr (fun hc => ?_)
            rw [hc] at h3; simp at h3
          have hnn : ‖ξ₁‖ = ‖ξ₂‖ :=
            hrpowinj _ _ (norm_nonneg _) (norm_nonneg _)
              (mul_right_cancel₀ (ne_of_gt hKp) hmod)
          have e1 := Complex.norm_mul_exp_arg_mul_I ξ₁
          have e2 := Complex.norm_mul_exp_arg_mul_I ξ₂
          rw [← e1, ← e2, hnn, hargeq]
    · -- ## Step 6: surjectivity
      intro z
      rcases eq_or_ne z 0 with hz | hz
      · exact ⟨0, by rw [hH0, hz]⟩
      · obtain ⟨θ, hθ⟩ := hΘsurj (Complex.arg z)
        have hKp : 0 < ‖1 + w θ‖ := by
          have h3 : 0 < (1 + w θ).re := by linarith [hre θ]
          refine norm_pos_iff.mpr (fun hc => ?_)
          rw [hc] at h3; simp at h3
        obtain ⟨s, hsdef⟩ : ∃ x : ℝ, x = ‖z‖ / ‖1 + w θ‖ := ⟨_, rfl⟩
        have hs : 0 < s := by
          rw [hsdef]; exact div_pos (norm_pos_iff.mpr hz) hKp
        have hsK : s * ‖1 + w θ‖ = ‖z‖ := by
          rw [hsdef]; field_simp
        obtain ⟨r, hrdef⟩ : ∃ x : ℝ, x = s ^ DExp p := ⟨_, rfl⟩
        have hr : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos hs _
        have hra : r ^ a = s := by
          rw [hrdef, ← Real.rpow_mul hs.le, hadef, mul_one_div, div_self hd.ne',
            Real.rpow_one]
        refine ⟨(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), ?_⟩
        have hpf := (ExtremalPolarForm p hp).1 r hr θ
        rw [← hepsdef, hGsplit θ, hpolar θ, ← hadef, hra] at hpf
        rw [hpf, hθ]
        have hfin : ((s : ℝ) : ℂ) * (((‖1 + w θ‖ : ℝ) : ℂ)
            * Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I))
            = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) := by
          rw [← hsK]
          push_cast
          ring
        rw [hfin]
        exact Complex.norm_mul_exp_arg_mul_I z
  -- ## Step 7: `H` is a closed map.  The lower bound of (6) makes `H` proper:
  -- a sequence with `H ξ_k` bounded has `‖ξ_k‖ ^ a` bounded, hence `(ξ_k)` bounded,
  -- so Bolzano-Weierstrass gives a convergent subsequence inside the closed set.
  have hclosed : IsClosedMap (ExtremalH p) := by
    intro C hC
    refine IsSeqClosed.isClosed (fun u y hu hconv => ?_)
    -- pick preimages
    choose ξ hξC hξH using fun n => hu n
    -- `(‖u n‖)` is bounded, so by the lower bound of (6) so is `(‖ξ n‖)`
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ n, ‖u n‖ ≤ R := by
      obtain ⟨R, hRu⟩ := (hconv.norm).bddAbove_range
      exact ⟨R, fun n => hRu ⟨n, rfl⟩⟩
    obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = R / (1 - |eps|) := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by
      rw [hMdef]
      refine div_nonneg (le_trans (norm_nonneg (u 0)) (hR 0)) (by linarith)
    have hbnd : ∀ n, ‖ξ n‖ ≤ M ^ (1 / a) := by
      intro n
      have hrp : ‖ξ n‖ ^ a ≤ M := by
        rcases eq_or_ne (ξ n) 0 with h | h
        · rw [h]
          simpa [Real.zero_rpow hapos.ne'] using hM0
        · have h1 := (hHbound (ξ n) h).1
          rw [hξH n] at h1
          have h2 : (1 - |eps|) * ‖ξ n‖ ^ a ≤ R := le_trans h1 (hR n)
          rw [hMdef, le_div_iff₀ (by linarith : (0:ℝ) < 1 - |eps|)]
          linarith [h2]
      have h3 : (‖ξ n‖ ^ a) ^ (1 / a) ≤ M ^ (1 / a) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hrp (by positivity)
      rwa [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hapos.ne',
        Real.rpow_one] at h3
    -- bounded sequence in a compact ball: extract a convergent subsequence
    have hmem : ∀ n, ξ n ∈ Metric.closedBall (0 : ℂ) (M ^ (1 / a)) := by
      intro n
      simpa [Metric.mem_closedBall] using hbnd n
    obtain ⟨x, -, φ, hφ, hlim⟩ :=
      (isCompact_closedBall (0 : ℂ) (M ^ (1 / a))).tendsto_subseq hmem
    -- the limit lies in `C`, and `H` carries it to `y`
    have hxC : x ∈ C := hC.mem_of_tendsto hlim (Filter.Eventually.of_forall
      (fun i => hξC (φ i)))
    refine ⟨x, hxC, ?_⟩
    have hHx : Filter.Tendsto (fun i => ExtremalH p (ξ (φ i))) Filter.atTop
        (nhds (ExtremalH p x)) := (hHcont.continuousAt).tendsto.comp hlim
    have huy : Filter.Tendsto (fun i => ExtremalH p (ξ (φ i))) Filter.atTop (nhds y) := by
      have h := hconv.comp hφ.tendsto_atTop
      refine h.congr (fun i => ?_)
      exact (hξH (φ i)).symm
    exact tendsto_nhds_unique hHx huy
  -- ## Assembly: the inverse of the bijection, and its continuity from closedness
  obtain ⟨g, hgl, hgr⟩ : ∃ g : ℂ → ℂ, (∀ ξ : ℂ, g (ExtremalH p ξ) = ξ)
      ∧ (∀ z : ℂ, ExtremalH p (g z) = z) := by
    refine ⟨Function.invFun (ExtremalH p), ?_, ?_⟩
    · intro ξ; exact Function.leftInverse_invFun hbij.injective ξ
    · intro z; exact Function.invFun_eq (hbij.surjective z)
  have hgcont : Continuous g := by
    refine continuous_iff_isClosed.mpr (fun C hC => ?_)
    have himg : g ⁻¹' C = ExtremalH p '' C := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨g z, h, hgr z⟩
      · rintro ⟨ξ, hξC, hξ⟩
        rw [← hξ, hgl ξ]
        exact hξC
    rw [himg]
    exact hclosed C hC
  exact ⟨hHcont, hbij, g, hgcont, hgl, hgr⟩
