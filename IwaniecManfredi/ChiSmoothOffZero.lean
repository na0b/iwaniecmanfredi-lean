import IwaniecManfredi.Preamble
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-- A continuous `m`-th root of a `C^∞` nonvanishing function is `C^∞`.  This
is the regularity of the quasiconformal factor `χ` of the factorization (15)
away from the singular point: `paper.tex:179-181` differentiates `χ` (and
Lemma 1 differentiates it arbitrarily often), while the factorization theorem
quoted in (C2) supplies only that `χ` is a quasiconformal homeomorphism, hence
only continuity.  Smoothness comes from here, applied on the punctured
neighbourhood where (C3) makes `f` smooth and discreteness of the zero set
makes it nonvanishing: locally a `C^∞` branch of `f^{1/m}` exists because `f`
omits `0`, and a continuous `m`-th root differs from that branch by a
continuous `m`-th root of unity, hence locally by a constant. -/
theorem ChiSmoothOffZero (m : ℕ) (hm : 1 ≤ m) (U : Set ℂ) (hU : IsOpen U)
    (f chi : ℂ → ℂ)
    (hchi : ContinuousOn chi U)
    (hfact : ∀ z ∈ U, f z = chi z ^ m)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hfne : ∀ z ∈ U, f z ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) chi U := by
  have hm0 : m ≠ 0 := by omega
  -- the `m`-th roots of unity form a finite set: the roots of `X^m - 1`
  have hSfin : {ω : ℂ | ω ^ m = 1}.Finite := by
    have hp : (Polynomial.X ^ m - 1 : Polynomial ℂ) ≠ 0 := by
      intro h
      have h0 : (Polynomial.X ^ m - 1 : Polynomial ℂ).eval 0 = 0 := by rw [h]; simp
      simp [zero_pow hm0] at h0
    refine (Polynomial.finite_setOfPred_isRoot hp).subset (fun ω hω => ?_)
    have hω' : ω ^ m = 1 := hω
    show (Polynomial.X ^ m - 1 : Polynomial ℂ).IsRoot ω
    simp [Polynomial.IsRoot, hω']
  -- ## Step 0: smoothness on an open set is local
  refine contDiffOn_of_locally_contDiffOn ?_
  intro z₁ hz₁
  -- ## Step 1: a holomorphic `m`-th root on the disc `D` about `w₁ = f z₁`
  obtain ⟨w₁, hw₁def⟩ : ∃ x : ℂ, x = f z₁ := ⟨_, rfl⟩
  have hw₁ne : w₁ ≠ 0 := by rw [hw₁def]; exact hfne z₁ hz₁
  have hw₁pos : 0 < ‖w₁‖ := norm_pos_iff.mpr hw₁ne
  obtain ⟨φ, hφdef⟩ : ∃ g : ℂ → ℂ, g = fun x : ℂ =>
      Complex.exp ((Complex.log w₁ + Complex.log (x / w₁)) / (m : ℂ)) := ⟨_, rfl⟩
  -- `|ζ - 1| < 1` forces `0 < Re ζ`, so `w / w₁` is in the slit plane
  have hslit : ∀ w ∈ Metric.ball w₁ ‖w₁‖, (w / w₁) ∈ Complex.slitPlane := by
    intro w hw
    have hwd : ‖w - w₁‖ < ‖w₁‖ := by
      have hdd := Metric.mem_ball.mp hw
      rwa [dist_eq_norm] at hdd
    have hz1 : ‖w / w₁ - 1‖ < 1 := by
      have he : w / w₁ - 1 = (w - w₁) / w₁ := by field_simp
      rw [he, norm_div, div_lt_one hw₁pos]
      exact hwd
    rw [Complex.mem_slitPlane_iff]
    refine Or.inl ?_
    have h2 : ‖w / w₁ - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (w / w₁ - 1)]
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
    nlinarith [sq_nonneg (w / w₁).re, sq_nonneg (w / w₁).im]
  have hDne : ∀ w ∈ Metric.ball w₁ ‖w₁‖, w ≠ 0 := by
    intro w hw hw0
    have hdd := Metric.mem_ball.mp hw
    rw [dist_eq_norm, hw0, zero_sub, norm_neg] at hdd
    exact absurd hdd (lt_irrefl _)
  have hφcd : ContDiffOn ℝ (⊤ : ℕ∞) φ (Metric.ball w₁ ‖w₁‖) := by
    intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    rw [hφdef]
    have hdiv : ContDiffAt ℂ (⊤ : ℕ∞) (fun x : ℂ => x / w₁) w := contDiffAt_id.div_const w₁
    have hlogc : ContDiffAt ℂ (⊤ : ℕ∞) (fun x : ℂ => Complex.log (x / w₁)) w := by
      have hcc := ContDiffAt.comp w (Complex.contDiffAt_log (hslit w hw)) hdiv
      exact hcc
    have hC : ContDiffAt ℂ (⊤ : ℕ∞) (fun x : ℂ =>
        Complex.exp ((Complex.log w₁ + Complex.log (x / w₁)) / (m : ℂ))) w :=
      Complex.contDiff_exp.contDiffAt.comp w ((contDiffAt_const.add hlogc).div_const _)
    exact hC.restrict_scalars ℝ
  have hφpow : ∀ w ∈ Metric.ball w₁ ‖w₁‖, φ w ^ m = w := by
    intro w hw
    have hmne : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    have hdne : w / w₁ ≠ 0 := div_ne_zero (hDne w hw) hw₁ne
    have hkey : ((m : ℂ)) * ((Complex.log w₁ + Complex.log (w / w₁)) / (m : ℂ))
        = Complex.log w₁ + Complex.log (w / w₁) := by field_simp
    simp only [hφdef]
    rw [← Complex.exp_nat_mul, hkey, Complex.exp_add, Complex.exp_log hw₁ne,
      Complex.exp_log hdne]
    field_simp
  -- ## Step 2: a ball `B` about `z₁` inside `U` on which `f` takes values in `D`
  have hfca : ContinuousAt f z₁ := hf.continuousOn.continuousAt (hU.mem_nhds hz₁)
  have hDnhd : Metric.ball w₁ ‖w₁‖ ∈ nhds (f z₁) := by
    rw [← hw₁def]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hw₁pos)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hfca hDnhd) (hU.mem_nhds hz₁))
  have hBU : Metric.ball z₁ r ⊆ U := fun z hz => (hrsub hz).2
  have hBD : ∀ z ∈ Metric.ball z₁ r, f z ∈ Metric.ball w₁ ‖w₁‖ := fun z hz => (hrsub hz).1
  -- ## Step 3: `ψ = φ ∘ f` is a `C^∞` nonvanishing `m`-th root of `f` on `B`
  obtain ⟨ψ, hψdef⟩ : ∃ g : ℂ → ℂ, g = fun z : ℂ => φ (f z) := ⟨_, rfl⟩
  have hψcd : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Metric.ball z₁ r) := by
    rw [hψdef]
    exact hφcd.comp (hf.mono hBU) hBD
  have hψpow : ∀ z ∈ Metric.ball z₁ r, ψ z ^ m = f z := by
    intro z hz
    simp only [hψdef]
    exact hφpow (f z) (hBD z hz)
  have hψne : ∀ z ∈ Metric.ball z₁ r, ψ z ≠ 0 := by
    intro z hz
    simp only [hψdef, hφdef]
    exact Complex.exp_ne_zero _
  -- ## Step 4: `chi / ψ` is continuous with values in a FINITE set, on a preconnected
  -- set, hence constant
  have hqcont : ContinuousOn (fun z => chi z / ψ z) (Metric.ball z₁ r) :=
    ContinuousOn.div (hchi.mono hBU) hψcd.continuousOn hψne
  have hqpow : ∀ z ∈ Metric.ball z₁ r, (chi z / ψ z) ^ m = 1 := by
    intro z hz
    rw [div_pow, hψpow z hz, ← hfact z (hBU hz)]
    exact div_self (hfne z (hBU hz))
  have hBpre : IsPreconnected (Metric.ball z₁ r) := (convex_ball z₁ r).isPreconnected
  obtain ⟨ω₀, hω₀S, hω₀⟩ := hBpre.eqOn_const_of_mapsTo hSfin.isDiscrete hqcont
    (fun z hz => hqpow z hz) ⟨1, by simp⟩
  have hchieq : ∀ z ∈ Metric.ball z₁ r, chi z = ω₀ * ψ z := by
    intro z hz
    have h := hω₀ hz
    simp only [Function.const_apply] at h
    rw [div_eq_iff (hψne z hz)] at h
    exact h
  -- ## Step 5: conclusion on `B`
  refine ⟨Metric.ball z₁ r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
  rw [Set.inter_eq_self_of_subset_right hBU]
  exact ((contDiffOn_const (c := ω₀)).mul hψcd).congr hchieq
