import IwaniecManfredi.SolvesEq18
import IwaniecManfredi.DZ
import IwaniecManfredi.DZbar
import IwaniecManfredi.QuasiconformalOn
import IwaniecManfredi.PartialWord
import IwaniecManfredi.WeakPartialEqFDerivAE

open MeasureTheory

/-- The rescaling reduction that opens the proof of Corollary 1: if `H` is a
quasiconformal solution of (18) on an open set `V` containing the closed disk
of radius `t`, then `ζ ↦ H(tζ)` is a quasiconformal solution of (18) on the
unit disk which meets every hypothesis of Theorem 2, and its partial
derivatives are those of `H` scaled by `t^{|w|}`.  This is the paper's "By
rescaling the variable `ξ` one may assume without loss of generality that `H`
is a quasiconformal solution of (18) on the unit disk" (`paper.tex:376`),
licensed at `paper.tex:183`; the `W^{1,2}` and finite-energy clauses are what
makes the "without loss of generality" legitimate, and the derivative scaling
is what transports the conclusions of Corollary 1 back to `H`. -/
theorem Eq18Rescale (n : ℕ) (p : ℝ) (K t : ℝ) (hp : 1 < p) (hK : 1 ≤ K) (ht : 0 < t)
    (V : Set ℂ) (hV : IsOpen V) (hball : Metric.closedBall (0 : ℂ) t ⊆ V)
    (H : ℂ → ℂ)
    (hcont : ContinuousOn H V)
    (hdiff : ∀ᵐ ξ : ℂ, ξ ∈ V → DifferentiableAt ℝ H ξ)
    (hqc : QuasiconformalOn K V H)
    (h18 : SolvesEq18 n p V H) :
    ContinuousOn (fun ζ : ℂ => H ((t : ℂ) * ζ)) {ξ : ℂ | ‖ξ‖ < 1} ∧
    (∀ᵐ ζ : ℂ, ζ ∈ {ξ : ℂ | ‖ξ‖ < 1} →
      DifferentiableAt ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ) ∧
    SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) ∧
    MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) ∧
    IntegrableOn (fun ζ : ℂ =>
        ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2
          + ‖DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2)
      {ξ : ℂ | ‖ξ‖ < 1} volume ∧
    QuasiconformalOn K {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) ∧
    (ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : ℂ => H ((t : ℂ) * ζ)) ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) →
      ContDiffOn ℝ (⊤ : ℕ∞) H {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} ∧
        ∀ (w : List (Fin 2)) (ζ : ℂ), 0 < ‖ζ‖ → ‖ζ‖ < 1 →
          PartialWord w H ((t : ℂ) * ζ)
            = ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord w (fun z : ℂ => H ((t : ℂ) * z)) ζ) := by
  -- ## Step 0: the scaling map `s ζ = t ζ`
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have htcne : (t : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using htne
  have hsmul : ∀ z : ℂ, (t : ℂ) * z = (t : ℝ) • z := fun z => Complex.real_smul.symm
  have hseq : (fun z : ℂ => (t : ℂ) * z) = fun z : ℂ => (t : ℝ) • z := funext hsmul
  have hsnorm : ∀ z : ℂ, ‖(t : ℂ) * z‖ = t * ‖z‖ := by
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hsHFD : ∀ ζ : ℂ, HasFDerivAt (fun z : ℂ => (t : ℂ) * z)
      ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ)) ζ := by
    intro ζ
    have hid : HasFDerivAt (fun z : ℂ => z) (ContinuousLinearMap.id ℝ ℂ) ζ :=
      hasFDerivAt_id ζ
    exact hid.const_mul (t : ℂ)
  have hscd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (t : ℂ) * z) := by fun_prop
  -- `s` maps the unit disc into `V`, and misses `0` off the origin
  have hsV : ∀ ζ : ℂ, ‖ζ‖ < 1 → (t : ℂ) * ζ ∈ V := by
    intro ζ hζ
    refine hball ?_
    simp only [Metric.mem_closedBall, dist_zero_right, hsnorm ζ]
    nlinarith only [hζ, ht, norm_nonneg ζ]
  have hsW : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 →
      ((t : ℂ) * ζ) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} := by
    intro ζ h1 h2
    refine ⟨?_, ?_⟩
    · rw [hsnorm ζ]; positivity
    · rw [hsnorm ζ]; nlinarith only [h2, ht, norm_nonneg ζ]
  -- the chain rule for `f ∘ s`, in the one form every later step uses
  have hfdscale : ∀ (f : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ f ((t : ℂ) * ζ) →
      ∀ v : ℂ, fderiv ℝ (fun z : ℂ => f ((t : ℂ) * z)) ζ v
        = (t : ℂ) * fderiv ℝ f ((t : ℂ) * ζ) v := by
    intro f ζ hf v
    have hchain : HasFDerivAt (fun z : ℂ => f ((t : ℂ) * z))
        ((fderiv ℝ f ((t : ℂ) * ζ)).comp ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ))) ζ :=
      (hf.hasFDerivAt).comp ζ (hsHFD ζ)
    have hsm : ((t : ℂ) • (ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ) v = (t : ℝ) • v := by
      simp [Complex.real_smul]
    rw [hchain.fderiv, ContinuousLinearMap.comp_apply, hsm, map_smul, Complex.real_smul]
  have hcompdiff : ∀ (f : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ f ((t : ℂ) * ζ) →
      DifferentiableAt ℝ (fun z : ℂ => f ((t : ℂ) * z)) ζ :=
    fun f ζ hf => (hf.hasFDerivAt.comp ζ (hsHFD ζ)).differentiableAt
  -- ## Step 1: conjunct (a)
  have hGa : ContinuousOn (fun ζ : ℂ => H ((t : ℂ) * ζ)) {ξ : ℂ | ‖ξ‖ < 1} :=
    hcont.comp hscd.continuous.continuousOn (fun ζ hζ => hsV ζ hζ)
  -- ## Step 2: conjunct (b).  The pushforward of `volume` under `s` is a positive
  -- multiple of `volume`, so `s` is quasi-measure-preserving and null sets pull back.
  have hqmp : Measure.QuasiMeasurePreserving (fun ζ : ℂ => (t : ℂ) * ζ) volume volume := by
    rw [hseq]
    refine ⟨measurable_const_smul _, ?_⟩
    rw [Measure.map_addHaar_smul volume htne]
    exact Measure.smul_absolutelyContinuous
  have hGb : ∀ᵐ ζ : ℂ, ζ ∈ {ξ : ℂ | ‖ξ‖ < 1} →
      DifferentiableAt ℝ (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
    filter_upwards [hqmp.ae hdiff] with ζ hζ hmem
    exact hcompdiff H ζ (hζ (hsV ζ hmem))
  -- ## Step 4: the Wirtinger derivatives scale by `t`
  have hDZscale : ∀ (f : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ f ((t : ℂ) * ζ) →
      DZ (fun z : ℂ => f ((t : ℂ) * z)) ζ = (t : ℂ) * DZ f ((t : ℂ) * ζ) ∧
        DZbar (fun z : ℂ => f ((t : ℂ) * z)) ζ = (t : ℂ) * DZbar f ((t : ℂ) * ζ) := by
    intro f ζ hf
    have h1 := hfdscale f ζ hf 1
    have h2 := hfdscale f ζ hf Complex.I
    constructor
    · simp only [DZ, h1, h2]; ring
    · simp only [DZbar, h1, h2]; ring
  -- ## Step 4': the weak and the classical Wirtinger derivatives agree a.e.
  have hWC : ∀ Ω : Set ℂ, IsOpen Ω → ∀ u a b : ℂ → ℂ,
      IsWeakWirtingerOn Ω u a b → (∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ u z) →
      ∀ᵐ z : ℂ, z ∈ Ω → a z = DZ u z ∧ b z = DZbar u z := by
    intro Ω hΩ u a b hww hud
    obtain ⟨fx, fy, hu1, hx1, hy1, hwx, hwy, ha, hb⟩ := hww
    have hDfam : ∀ j : Fin 2,
        MemLpLocOn 1 Ω ((fun j : Fin 2 => if j = 0 then fx else fy) j) := by
      intro j
      fin_cases j
      · simpa using hx1
      · simpa using hy1
    have hweak : ∀ j : Fin 2,
        IsWeakPartialOn Ω j u ((fun j : Fin 2 => if j = 0 then fx else fy) j) := by
      intro j
      fin_cases j
      · simpa using hwx
      · simpa using hwy
    have hres := WeakPartialEqFDerivAE Ω hΩ u
      (fun j : Fin 2 => if j = 0 then fx else fy) hu1 hDfam hweak hud
    filter_upwards [hres 0, hres 1] with z h0 h1 hz
    have e0 : fx z = PartialWord [0] u z := by simpa using h0 hz
    have e1 : fy z = PartialWord [1] u z := by simpa using h1 hz
    refine ⟨?_, ?_⟩
    · rw [ha z, e0, e1]
      simp only [PartialWord, List.foldr, DZ]
      norm_num
    · rw [hb z, e0, e1]
      simp only [PartialWord, List.foldr, DZbar]
      norm_num
  -- the two open sets of Step 10
  have hBopen : IsOpen ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) :=
    (isOpen_lt continuous_norm continuous_const).sdiff isClosed_singleton
  have hWopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  -- every iterated partial derivative of a `C^∞` function on an open set is `C^∞` there
  have hPWcd : ∀ (w : List (Fin 2)) (f : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      ContDiffOn ℝ (⊤ : ℕ∞) f U → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) U := by
    intro w
    induction w with
    | nil => intro f U _ hf; exact hf
    | cons j w ih =>
        intro f U hU hf
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) U := ih f U hU hf
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w f)) U :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  -- ## Step 6 preparation: the change of variables.  The Jacobian constant is never
  -- evaluated: `MemLp` is a finiteness statement, and in the test-function identity the
  -- constant multiplies both sides.
  have hcHFD : ∀ (c : ℝ) (ζ : ℂ), HasFDerivAt (fun z : ℂ => (c : ℂ) * z)
      ((c : ℂ) • (ContinuousLinearMap.id ℝ ℂ)) ζ := by
    intro c ζ
    have hid : HasFDerivAt (fun z : ℂ => z) (ContinuousLinearMap.id ℝ ℂ) ζ :=
      hasFDerivAt_id ζ
    exact hid.const_mul (c : ℂ)
  have hcfd : ∀ (c : ℝ) (f : ℂ → ℂ) (ζ : ℂ), DifferentiableAt ℝ f ((c : ℂ) * ζ) →
      ∀ v : ℂ, fderiv ℝ (fun z : ℂ => f ((c : ℂ) * z)) ζ v
        = (c : ℂ) * fderiv ℝ f ((c : ℂ) * ζ) v := by
    intro c f ζ hf v
    have hchain : HasFDerivAt (fun z : ℂ => f ((c : ℂ) * z))
        ((fderiv ℝ f ((c : ℂ) * ζ)).comp ((c : ℂ) • (ContinuousLinearMap.id ℝ ℂ))) ζ :=
      (hf.hasFDerivAt).comp ζ (hcHFD c ζ)
    have hsm : ((c : ℂ) • (ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ) v = (c : ℝ) • v := by
      simp [Complex.real_smul]
    rw [hchain.fderiv, ContinuousLinearMap.comp_apply, hsm, map_smul, Complex.real_smul]
  have hcvint : ∀ f : ℂ → ℂ, (∫ x : ℂ, f ((t : ℂ) * x))
      = ((((t : ℝ) ^ Module.finrank ℝ ℂ)⁻¹ : ℝ)) • ∫ x : ℂ, f x := by
    intro f
    have h := Measure.integral_comp_smul_of_nonneg volume f t (hR := ht.le)
    simpa only [← hsmul] using h
  have hMemLpS : ∀ (q : ENNReal) (f : ℂ → ℂ), MemLp f q volume →
      MemLp (fun ζ : ℂ => f ((t : ℂ) * ζ)) q volume := by
    intro q f hf
    have hmap : Measure.map (fun ζ : ℂ => (t : ℝ) • ζ) volume
        = ENNReal.ofReal |((t : ℝ) ^ Module.finrank ℝ ℂ)⁻¹| • volume :=
      Measure.map_addHaar_smul volume htne
    have h1 : MemLp f q (Measure.map (fun ζ : ℂ => (t : ℝ) • ζ) volume) := by
      rw [hmap]; exact hf.smul_measure ENNReal.ofReal_ne_top
    have h2 := (memLp_map_measure_iff h1.aestronglyMeasurable
      (measurable_const_smul _).aemeasurable).mp h1
    have he : (fun ζ : ℂ => f ((t : ℂ) * ζ)) = fun ζ : ℂ => f ((t : ℝ) • ζ) := by
      funext ζ; rw [hsmul ζ]
    rw [he]
    exact h2
  have hsinj : Function.Injective (fun ζ : ℂ => (t : ℂ) * ζ) :=
    fun a b hab => mul_left_cancel₀ htcne hab
  have hLploc : ∀ (q : ENNReal) (g : ℂ → ℂ), MemLpLocOn q V g →
      MemLpLocOn q {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => g ((t : ℂ) * ζ)) := by
    intro q g hg κ hκB hκcpt
    have himg : IsCompact ((fun ζ : ℂ => (t : ℂ) * ζ) '' κ) :=
      hκcpt.image (by fun_prop)
    have himgV : ((fun ζ : ℂ => (t : ℂ) * ζ) '' κ) ⊆ V := by
      intro z hz
      obtain ⟨ζ, hζ, hzz⟩ := hz
      rw [← hzz]
      exact hsV ζ (hκB hζ)
    have h3 := hMemLpS q _ (hg _ himgV himg)
    have heq : κ.indicator (fun ζ : ℂ => g ((t : ℂ) * ζ))
        = fun ζ : ℂ => ((fun ζ : ℂ => (t : ℂ) * ζ) '' κ).indicator g ((t : ℂ) * ζ) := by
      funext ζ
      by_cases hζ : ζ ∈ κ
      · rw [Set.indicator_of_mem hζ, Set.indicator_of_mem (Set.mem_image_of_mem _ hζ)]
      · have hnot : ((t : ℂ) * ζ) ∉ (fun ζ : ℂ => (t : ℂ) * ζ) '' κ := by
          intro hcon
          obtain ⟨ζ', hζ', heq'⟩ := hcon
          exact hζ (by rwa [hsinj heq'] at hζ')
        rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem hnot]
    rw [heq]
    exact h3
  have hLpconst : ∀ (q : ENNReal) (c : ℂ) (Ω : Set ℂ) (g : ℂ → ℂ), MemLpLocOn q Ω g →
      MemLpLocOn q Ω (fun z : ℂ => c * g z) := by
    intro q c Ω g hg κ hκ hκc
    have h := (hg κ hκ hκc).const_mul c
    have he : κ.indicator (fun z : ℂ => c * g z) = fun z : ℂ => c * κ.indicator g z := by
      funext z
      by_cases hz : z ∈ κ
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
    rw [he]
    exact h
  obtain ⟨hqr, hinj, -, hHopen, psi, hpsi, hpsic⟩ := hqc
  obtain ⟨D, hD0, hDLp, hDweak⟩ := hqr.2.1
  obtain ⟨D', hD'nil, hD'one, hD'big⟩ : ∃ D' : List (Fin 2) → (ℂ → ℂ),
      D' [] = (fun ζ : ℂ => H ((t : ℂ) * ζ)) ∧
      (∀ j : Fin 2, D' [j] = fun ζ : ℂ => (t : ℂ) * D [j] ((t : ℂ) * ζ)) ∧
      (∀ w : List (Fin 2), 2 ≤ w.length → D' w = 0) := by
    refine ⟨fun w => match w with
      | [] => fun ζ : ℂ => H ((t : ℂ) * ζ)
      | [j] => fun ζ : ℂ => (t : ℂ) * D [j] ((t : ℂ) * ζ)
      | _ :: _ :: _ => 0, rfl, fun _ => rfl, ?_⟩
    intro w hw
    match w with
    | [] => simp at hw
    | [j] => simp at hw
    | _ :: _ :: _ => rfl
  have hHV : MemLpLocOn 2 V H := by
    have h := hDLp [] (by simp)
    rwa [hD0] at h
  -- the transported test function, in full
  have hψtest : ∀ φ : ℂ → ℂ, IsTestFn {ξ : ℂ | ‖ξ‖ < 1} φ →
      IsTestFn V (fun z : ℂ => φ (((t⁻¹ : ℝ) : ℂ) * z)) := by
    intro φ hφ
    obtain ⟨hφsm, hφcs, hφsupp⟩ := hφ
    have hinvpos : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
    refine ⟨hφsm.comp (by fun_prop), ?_, ?_⟩
    · have he : (fun z : ℂ => φ (((t⁻¹ : ℝ) : ℂ) * z))
          = fun z : ℂ => φ ((t⁻¹ : ℝ) • z) := by
        funext z
        rw [Complex.real_smul]
      rw [he]
      exact hφcs.comp_smul (inv_ne_zero htne)
    · have hsupp : Function.support (fun z : ℂ => φ (((t⁻¹ : ℝ) : ℂ) * z))
          ⊆ {z : ℂ | ‖z‖ < t} := by
        intro z hz
        have h1 : (((t⁻¹ : ℝ) : ℂ) * z) ∈ Function.support φ := hz
        have h2 : (((t⁻¹ : ℝ) : ℂ) * z) ∈ {ξ : ℂ | ‖ξ‖ < 1} :=
          hφsupp (subset_closure h1)
        simp only [Set.mem_ofPred_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hinvpos] at h2
        simp only [Set.mem_ofPred_eq]
        rw [inv_mul_lt_iff₀ ht] at h2
        linarith only [h2]
      refine Set.Subset.trans (closure_mono hsupp) ?_
      refine Set.Subset.trans (closure_minimal ?_ Metric.isClosed_closedBall) hball
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hz
  -- ## Step 6: the two `L²` clauses and the weak-derivative clause for `D'`
  have hLpG : MemLpLocOn 2 {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) :=
    hLploc 2 H hHV
  have hLpD2 : ∀ j : Fin 2, MemLpLocOn 2 {ξ : ℂ | ‖ξ‖ < 1} (D' [j]) := by
    intro j
    rw [hD'one j]
    exact hLpconst 2 (t : ℂ) _ _ (hLploc 2 (D [j]) (hDLp [j] (by simp)))
  have hweakG : ∀ j : Fin 2, IsWeakPartialOn {ξ : ℂ | ‖ξ‖ < 1} j
      (fun ζ : ℂ => H ((t : ℂ) * ζ)) (D' [j]) := by
      intro j
      rw [hD'one j]
      intro φ hφ
      -- the transported test function and the two constants
      obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = ((t⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
      have htinv : c * (t : ℂ) = 1 := by
        rw [hcdef]
        push_cast
        field_simp
      obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = fun z : ℂ => φ (c * z) := ⟨_, rfl⟩
      have hψT : IsTestFn V ψ := by
        rw [hψdef, hcdef]
        exact hψtest φ hφ
      have hφdiff : ∀ z : ℂ, DifferentiableAt ℝ φ z :=
        fun z => (hφ.1.differentiable (by norm_num)).differentiableAt
      have hψval : ∀ ζ : ℂ, ψ ((t : ℂ) * ζ) = φ ζ := by
        intro ζ
        simp only [hψdef]
        congr 1
        rw [← mul_assoc, htinv, one_mul]
      have hψfd : ∀ ζ : ℂ,
          fderiv ℝ ψ ((t : ℂ) * ζ) (if j = 0 then (1 : ℂ) else Complex.I)
            = c * fderiv ℝ φ ζ (if j = 0 then (1 : ℂ) else Complex.I) := by
        intro ζ
        have hcc : ∃ d : ℝ, c = (d : ℂ) := ⟨t⁻¹, hcdef⟩
        obtain ⟨d, hd⟩ := hcc
        have h := hcfd d φ ((t : ℂ) * ζ) (hφdiff _)
          (if j = 0 then (1 : ℂ) else Complex.I)
        rw [← hd] at h
        simp only [hψdef]
        rw [h, ← mul_assoc, htinv, one_mul]
      -- the two change-of-variables identities
      obtain ⟨Cc, hCcdef⟩ : ∃ x : ℂ,
          x = ((((t : ℝ) ^ Module.finrank ℝ ℂ)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
      obtain ⟨IG, hIG⟩ : ∃ x : ℂ, x = ∫ ζ : ℂ,
          H ((t : ℂ) * ζ) * fderiv ℝ φ ζ (if j = 0 then (1 : ℂ) else Complex.I) := ⟨_, rfl⟩
      obtain ⟨IDφ, hIDφ⟩ : ∃ x : ℂ,
          x = ∫ ζ : ℂ, D [j] ((t : ℂ) * ζ) * φ ζ := ⟨_, rfl⟩
      obtain ⟨IDψ, hIDψ⟩ : ∃ x : ℂ, x = ∫ z : ℂ, D [j] z * ψ z := ⟨_, rfl⟩
      have hstar := hDweak [] j (by simp) ψ hψT
      rw [hD0, List.nil_append] at hstar
      have eq1 : c * IG = -(Cc * IDψ) := by
        have h1 := hcvint (fun z : ℂ =>
          H z * fderiv ℝ ψ z (if j = 0 then (1 : ℂ) else Complex.I))
        rw [hstar, Complex.real_smul, ← hCcdef, ← hIDψ] at h1
        have h2 : (∫ ζ : ℂ,
              H ((t : ℂ) * ζ) * fderiv ℝ ψ ((t : ℂ) * ζ)
                (if j = 0 then (1 : ℂ) else Complex.I))
            = c * IG := by
          rw [hIG, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
          simp only [hψfd ζ]
          ring
        rw [h2] at h1
        rw [h1]
        ring
      have eq2 : IDφ = Cc * IDψ := by
        have h1 := hcvint (fun z : ℂ => D [j] z * ψ z)
        rw [Complex.real_smul, ← hCcdef, ← hIDψ] at h1
        have h2 : (∫ ζ : ℂ, D [j] ((t : ℂ) * ζ) * ψ ((t : ℂ) * ζ)) = IDφ := by
          rw [hIDφ]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
          simp only [hψval ζ]
        rw [h2] at h1
        exact h1
      have hR : (∫ ζ : ℂ, ((t : ℂ) * D [j] ((t : ℂ) * ζ)) * φ ζ) = (t : ℂ) * IDφ := by
        rw [hIDφ, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
        ring
      rw [← hIG, hR, eq2]
      linear_combination (t : ℂ) * eq1 - IG * htinv
  -- ## conjunct (d)
  have hGd : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) := by
    refine ⟨D', hD'nil, ?_, ?_⟩
    · intro w hw
      rcases w with _ | ⟨j, w'⟩
      · rw [hD'nil]; exact hLpG
      · rcases w' with _ | ⟨j2, w''⟩
        · exact hLpD2 j
        · exfalso; simp at hw
    · intro w j hw
      have hwnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hwnil
      rw [hD'nil, List.nil_append]
      exact hweakG j
  -- ## Steps 5 and 7': conjunct (c)
  have hBo : IsOpen {ξ : ℂ | ‖ξ‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hholder : ∀ (Ω : Set ℂ) (g : ℂ → ℂ), MemLpLocOn 2 Ω g → MemLpLocOn 1 Ω g := by
    intro Ω g hg κ hκ hκc
    refine (hg κ hκ hκc).mono_exponent_of_measure_support_ne_top (s := κ) ?_ ?_ (by norm_num)
    · intro x hx
      exact Set.indicator_of_notMem hx g
    · exact (hκc.measure_lt_top).ne
  obtain ⟨aG, haG⟩ : ∃ f : ℂ → ℂ, ∀ z : ℂ,
      f z = (1 / 2 : ℂ) * (D' [0] z - Complex.I * D' [1] z) := ⟨_, fun _ => rfl⟩
  obtain ⟨bG, hbG⟩ : ∃ f : ℂ → ℂ, ∀ z : ℂ,
      f z = (1 / 2 : ℂ) * (D' [0] z + Complex.I * D' [1] z) := ⟨_, fun _ => rfl⟩
  have hwwG : IsWeakWirtingerOn {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) aG bG :=
    ⟨D' [0], D' [1], hholder _ _ hLpG, hholder _ _ (hLpD2 0), hholder _ _ (hLpD2 1),
      hweakG 0, hweakG 1, haG, hbG⟩
  have hGc : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) := by
    refine ⟨aG, bG, hwwG, ?_⟩
    obtain ⟨aH, bH, hwwH, hptH⟩ := h18
    have hWCH := hWC V hV H aH bH hwwH hdiff
    have hWCG := hWC {ξ : ℂ | ‖ξ‖ < 1} hBo (fun ζ : ℂ => H ((t : ℂ) * ζ)) aG bG hwwG hGb
    filter_upwards [hqmp.ae hWCH, hqmp.ae hptH, hqmp.ae hdiff, hWCG]
      with ζ h1 h2 h3 h4 hmem hne
    have hzV : ((t : ℂ) * ζ) ∈ V := hsV ζ hmem
    have hzne : ((t : ℂ) * ζ) ≠ 0 := mul_ne_zero htcne hne
    obtain ⟨e1, e2⟩ := h1 hzV
    obtain ⟨e3, e4⟩ := h4 hmem
    have hdH : DifferentiableAt ℝ H ((t : ℂ) * ζ) := h3 hzV
    obtain ⟨e5, e6⟩ := hDZscale H ζ hdH
    have hptz := h2 hzV hzne
    -- the two coefficient ratios are scale invariant
    have hcj : starRingEnd ℂ ((t : ℂ) * ζ) = (t : ℂ) * starRingEnd ℂ ζ := by
      rw [map_mul, Complex.conj_ofReal]
    have hr1 : ((t : ℂ) * ζ) / starRingEnd ℂ ((t : ℂ) * ζ) = ζ / starRingEnd ℂ ζ := by
      rw [hcj, mul_div_mul_left _ _ htcne]
    have hr2 : (starRingEnd ℂ ((t : ℂ) * ζ)) ^ n / ((t : ℂ) * ζ) ^ n
        = (starRingEnd ℂ ζ) ^ n / ζ ^ n := by
      rw [hcj, mul_pow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero n htcne)]
    rw [hr1, hr2] at hptz
    -- transport the identity
    have haGz : aG ζ = (t : ℂ) * aH ((t : ℂ) * ζ) := by rw [e3, e5, e1]
    have hbGz : bG ζ = (t : ℂ) * bH ((t : ℂ) * ζ) := by rw [e4, e6, e2]
    rw [hbGz, hptz, haGz, map_mul, Complex.conj_ofReal]
    ring
  -- ## Step 9: conjunct (f)
  have hGf : QuasiconformalOn K {ξ : ℂ | ‖ξ‖ < 1} (fun ζ : ℂ => H ((t : ℂ) * ζ)) := by
    -- the distortion inequality, transported
    obtain ⟨aH', bH', hwwH', hdist⟩ := hqr.2.2
    have hWCH' := hWC V hV H aH' bH' hwwH' hdiff
    have hWCG := hWC {ξ : ℂ | ‖ξ‖ < 1} hBo (fun ζ : ℂ => H ((t : ℂ) * ζ)) aG bG hwwG hGb
    have hdistG : ∀ᵐ ζ : ℂ, ζ ∈ {ξ : ℂ | ‖ξ‖ < 1} →
        ‖bG ζ‖ ≤ ((K - 1) / (K + 1)) * ‖aG ζ‖ := by
      filter_upwards [hqmp.ae hWCH', hqmp.ae hdist, hqmp.ae hdiff, hWCG]
        with ζ h1 h2 h3 h4 hmem
      have hzV : ((t : ℂ) * ζ) ∈ V := hsV ζ hmem
      obtain ⟨e1, e2⟩ := h1 hzV
      obtain ⟨e3, e4⟩ := h4 hmem
      obtain ⟨e5, e6⟩ := hDZscale H ζ (h3 hzV)
      have hd := h2 hzV
      have hbn : ‖bG ζ‖ = t * ‖bH' ((t : ℂ) * ζ)‖ := by
        rw [e4, e6, e2, hsnorm]
      have han : ‖aG ζ‖ = t * ‖aH' ((t : ℂ) * ζ)‖ := by
        rw [e3, e5, e1, hsnorm]
      rw [hbn, han]
      have hmul := mul_le_mul_of_nonneg_left hd ht.le
      linarith only [hmul]
    -- injectivity
    have hGinj : Set.InjOn (fun ζ : ℂ => H ((t : ℂ) * ζ)) {ξ : ℂ | ‖ξ‖ < 1} := by
      intro ζ₁ h₁ ζ₂ h₂ heq
      exact mul_left_cancel₀ htcne (hinj (hsV ζ₁ h₁) (hsV ζ₂ h₂) heq)
    -- the image, as the TeX's (6)
    have himage : (fun ζ : ℂ => H ((t : ℂ) * ζ)) '' {ξ : ℂ | ‖ξ‖ < 1}
        = (H '' V) ∩ psi ⁻¹' {z : ℂ | ‖z‖ < t} := by
      refine Set.Subset.antisymm ?_ ?_
      · intro w hw
        obtain ⟨ζ, hζ, hwz⟩ := hw
        refine ⟨⟨(t : ℂ) * ζ, hsV ζ hζ, hwz⟩, ?_⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        have hζ' : ‖ζ‖ < 1 := hζ
        rw [← hwz]
        show ‖psi (H ((t : ℂ) * ζ))‖ < t
        rw [hpsi _ (hsV ζ hζ), hsnorm]
        nlinarith only [hζ', ht, norm_nonneg ζ]
      · intro w hw
        obtain ⟨⟨z, hzV, hzw⟩, hwp⟩ := hw
        have hpz : psi w = z := by rw [← hzw]; exact hpsi z hzV
        have hzn : ‖z‖ < t := by
          have := hwp
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hpz] at this
          exact this
        refine ⟨((t : ℝ) : ℂ)⁻¹ * z, ?_, ?_⟩
        · simp only [Set.mem_ofPred_eq, norm_mul, norm_inv, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos ht]
          rw [inv_mul_lt_iff₀ ht]
          linarith only [hzn]
        · rw [← hzw]
          show H ((t : ℂ) * (((t : ℝ) : ℂ)⁻¹ * z)) = H z
          rw [← mul_assoc, mul_inv_cancel₀ htcne, one_mul]
    have hGopen : IsOpen ((fun ζ : ℂ => H ((t : ℂ) * ζ)) '' {ξ : ℂ | ‖ξ‖ < 1}) := by
      rw [himage]
      exact hpsic.isOpen_inter_preimage hHopen (isOpen_lt continuous_norm continuous_const)
    -- the inverse
    have hsubim : (fun ζ : ℂ => H ((t : ℂ) * ζ)) '' {ξ : ℂ | ‖ξ‖ < 1} ⊆ H '' V := by
      rw [himage]
      exact Set.inter_subset_left
    refine ⟨⟨hK, hGd, aG, bG, hwwG, hdistG⟩, hGinj, hGa, hGopen,
      fun w : ℂ => ((t : ℝ) : ℂ)⁻¹ * psi w, ?_, ?_⟩
    · intro ζ hζ
      show ((t : ℝ) : ℂ)⁻¹ * psi (H ((t : ℂ) * ζ)) = ζ
      rw [hpsi _ (hsV ζ hζ), ← mul_assoc, inv_mul_cancel₀ htcne, one_mul]
    · exact continuousOn_const.mul (hpsic.mono hsubim)
  -- ## Step 8: conjunct (e)
  have hpara : ∀ (u : ℂ → ℂ) (z : ℂ),
      ‖DZ u z‖ ^ 2 + ‖DZbar u z‖ ^ 2
        = (1 / 2 : ℝ) * (‖PartialWord [0] u z‖ ^ 2 + ‖PartialWord [1] u z‖ ^ 2) := by
    intro u z
    have h := parallelogram_law_with_norm ℝ (fderiv ℝ u z 1)
      (Complex.I * fderiv ℝ u z Complex.I)
    have hI : ‖Complex.I * fderiv ℝ u z Complex.I‖ = ‖fderiv ℝ u z Complex.I‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have hI2 : ‖Complex.I * fderiv ℝ u z Complex.I‖ ^ 2
        = ‖fderiv ℝ u z Complex.I‖ ^ 2 := by rw [hI]
    have hnDZ : ‖DZ u z‖
        = (1 / 2 : ℝ) * ‖fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I‖ := by
      simp only [DZ, norm_mul]
      norm_num
    have hnDZbar : ‖DZbar u z‖
        = (1 / 2 : ℝ) * ‖fderiv ℝ u z 1 + Complex.I * fderiv ℝ u z Complex.I‖ := by
      simp only [DZbar, norm_mul]
      norm_num
    show ‖DZ u z‖ ^ 2 + ‖DZbar u z‖ ^ 2
      = (1 / 2 : ℝ) * (‖fderiv ℝ u z 1‖ ^ 2 + ‖fderiv ℝ u z Complex.I‖ ^ 2)
    rw [hnDZ, hnDZbar]
    linear_combination (1 / 4 : ℝ) * h + (1 / 2 : ℝ) * hI2
  have hDHae : ∀ j : Fin 2, ∀ᵐ z : ℂ, z ∈ V → D [j] z = PartialWord [j] H z := by
    refine WeakPartialEqFDerivAE V hV H (fun j : Fin 2 => D [j])
      (hholder V H hHV) (fun j => hholder V _ (hDLp [j] (by simp))) (fun j => ?_) hdiff
    have h := hDweak [] j (by simp)
    rwa [hD0, List.nil_append] at h
  have hEae : ∀ᵐ ζ : ℂ, ζ ∈ {ξ : ℂ | ‖ξ‖ < 1} →
      ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2
          + ‖DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2
        = (t ^ 2 : ℝ) * ((1 / 2 : ℝ)
            * (‖D [0] ((t : ℂ) * ζ)‖ ^ 2 + ‖D [1] ((t : ℂ) * ζ)‖ ^ 2)) := by
    filter_upwards [hqmp.ae hdiff, hqmp.ae (hDHae 0), hqmp.ae (hDHae 1)]
      with ζ h1 h2 h3 hmem
    have hzV : ((t : ℂ) * ζ) ∈ V := hsV ζ hmem
    obtain ⟨e5, e6⟩ := hDZscale H ζ (h1 hzV)
    have hp := hpara H ((t : ℂ) * ζ)
    rw [← h2 hzV, ← h3 hzV] at hp
    rw [e5, e6, hsnorm, hsnorm]
    linear_combination (t ^ 2 : ℝ) * hp
  have hDsq : ∀ j : Fin 2, IntegrableOn (fun z : ℂ => ‖D [j] z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) t) volume := by
    intro j
    have h2 : MemLp ((Metric.closedBall (0 : ℂ) t).indicator (D [j])) 2 volume :=
      hDLp [j] (by simp) _ hball (isCompact_closedBall _ _)
    have h2' : MemLp ((Metric.closedBall (0 : ℂ) t).indicator (D [j]))
        (((2 : ℕ) : ENNReal)) volume := by simpa using h2
    have h3 := h2'.integrable_norm_pow (by norm_num)
    have he : (Metric.closedBall (0 : ℂ) t).indicator (fun z : ℂ => ‖D [j] z‖ ^ 2)
        = fun z : ℂ => ‖(Metric.closedBall (0 : ℂ) t).indicator (D [j]) z‖ ^ 2 := by
      funext z
      by_cases hz : z ∈ Metric.closedBall (0 : ℂ) t
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
        simp
    rw [← integrable_indicator_iff measurableSet_closedBall, he]
    exact h3
  have hBmeas : MeasurableSet {ξ : ℂ | ‖ξ‖ < 1} := hBo.measurableSet
  have hstep : ∀ j : Fin 2, IntegrableOn (fun ζ : ℂ => ‖D [j] ((t : ℂ) * ζ)‖ ^ 2)
      {ξ : ℂ | ‖ξ‖ < 1} volume := by
    intro j
    have h1 : IntegrableOn (fun z : ℂ => ‖D [j] z‖ ^ 2) (Metric.ball (0 : ℂ) t) volume :=
      (hDsq j).mono_set Metric.ball_subset_closedBall
    have h2 : Integrable
        ((Metric.ball (0 : ℂ) t).indicator (fun z : ℂ => ‖D [j] z‖ ^ 2)) volume :=
      (integrable_indicator_iff measurableSet_ball).mpr h1
    have h3 := h2.comp_smul (R := t) htne
    rw [← integrable_indicator_iff hBmeas]
    refine h3.congr ?_
    refine Filter.Eventually.of_forall (fun ζ => ?_)
    show (Metric.ball (0 : ℂ) t).indicator (fun z : ℂ => ‖D [j] z‖ ^ 2) ((t : ℝ) • ζ)
      = {ξ : ℂ | ‖ξ‖ < 1}.indicator (fun ζ : ℂ => ‖D [j] ((t : ℂ) * ζ)‖ ^ 2) ζ
    have hmemiff : ((t : ℝ) • ζ) ∈ Metric.ball (0 : ℂ) t ↔ ζ ∈ {ξ : ℂ | ‖ξ‖ < 1} := by
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      rw [mul_comm]
      constructor
      · intro h; nlinarith only [h, ht, norm_nonneg ζ]
      · intro h; nlinarith only [h, ht, norm_nonneg ζ]
    by_cases hζ : ζ ∈ {ξ : ℂ | ‖ξ‖ < 1}
    · rw [Set.indicator_of_mem (hmemiff.mpr hζ), Set.indicator_of_mem hζ, hsmul ζ]
    · rw [Set.indicator_of_notMem (fun hc => hζ (hmemiff.mp hc)),
        Set.indicator_of_notMem hζ]
  have hFint : IntegrableOn (fun ζ : ℂ => (t ^ 2 : ℝ) * ((1 / 2 : ℝ)
      * (‖D [0] ((t : ℂ) * ζ)‖ ^ 2 + ‖D [1] ((t : ℂ) * ζ)‖ ^ 2)))
      {ξ : ℂ | ‖ξ‖ < 1} volume :=
    (((hstep 0).add (hstep 1)).const_mul (1 / 2 : ℝ)).const_mul (t ^ 2 : ℝ)
  have hGe : IntegrableOn (fun ζ : ℂ =>
      ‖DZ (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2
        + ‖DZbar (fun z : ℂ => H ((t : ℂ) * z)) ζ‖ ^ 2)
      {ξ : ℂ | ‖ξ‖ < 1} volume := by
    refine hFint.congr ?_
    refine (MeasureTheory.ae_restrict_iff' hBmeas).mpr ?_
    filter_upwards [hEae] with ζ h hmem
    exact (h hmem).symm
  -- ## Step 10: conjunct (g)
  have hGg : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : ℂ => H ((t : ℂ) * ζ))
        ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) →
      ContDiffOn ℝ (⊤ : ℕ∞) H {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} ∧
        ∀ (w : List (Fin 2)) (ζ : ℂ), 0 < ‖ζ‖ → ‖ζ‖ < 1 →
          PartialWord w H ((t : ℂ) * ζ)
            = ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord w (fun z : ℂ => H ((t : ℂ) * z)) ζ := by
    intro hGsm
    have hσcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => ((t : ℝ) : ℂ)⁻¹ * z) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => ((t : ℝ) : ℂ)⁻¹ * z)
        {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
      intro z hz
      have hzn : ‖((t : ℝ) : ℂ)⁻¹ * z‖ = ‖z‖ / t := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
          div_eq_inv_mul]
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, hzn]
        rw [div_lt_one ht]
        exact hz.2
      · simp only [Set.mem_singleton_iff]
        intro hcon
        have h0 : ‖((t : ℝ) : ℂ)⁻¹ * z‖ = 0 := by rw [hcon, norm_zero]
        rw [hzn, div_eq_zero_iff] at h0
        rcases h0 with h | h
        · exact absurd h (ne_of_gt hz.1)
        · exact absurd h htne
    have hHsm : ContDiffOn ℝ (⊤ : ℕ∞) H {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t} := by
      refine (hGsm.comp hσcd.contDiffOn hmaps).congr ?_
      intro z _
      show H z = H ((t : ℂ) * (((t : ℝ) : ℂ)⁻¹ * z))
      rw [← mul_assoc, mul_inv_cancel₀ htcne, one_mul]
    refine ⟨hHsm, ?_⟩
    -- the derivative dictionary, by induction on the word
    intro w
    induction w with
    | nil =>
        intro ζ _ _
        simp only [PartialWord, List.foldr, List.length_nil, pow_zero, one_mul]
    | cons j w ih =>
        intro ζ h1 h2
        have hζmem : ζ ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
          refine ⟨h2, ?_⟩
          simp only [Set.mem_singleton_iff]
          exact norm_pos_iff.mp h1
        have hagree : ∀ z ∈ ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}),
            PartialWord w H ((t : ℂ) * z)
              = ((t : ℝ) : ℂ)⁻¹ ^ w.length
                  * PartialWord w (fun y : ℂ => H ((t : ℂ) * y)) z := by
          intro z hz
          refine ih z ?_ hz.1
          exact norm_pos_iff.mpr (by simpa using hz.2)
        have hfe : fderiv ℝ (fun z : ℂ => PartialWord w H ((t : ℂ) * z)) ζ
            = fderiv ℝ (fun z : ℂ => ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord w (fun y : ℂ => H ((t : ℂ) * y)) z) ζ :=
          Filter.EventuallyEq.fderiv_eq
            (Filter.eventuallyEq_of_mem (hBopen.mem_nhds hζmem) hagree)
        -- differentiability of the two sides
        have hHw : DifferentiableAt ℝ (PartialWord w H) ((t : ℂ) * ζ) :=
          ((hPWcd w H _ hWopen hHsm).differentiableOn (by norm_num)).differentiableAt
            (hWopen.mem_nhds (hsW ζ h1 h2))
        have hGw : DifferentiableAt ℝ (PartialWord w (fun y : ℂ => H ((t : ℂ) * y))) ζ :=
          ((hPWcd w _ _ hBopen hGsm).differentiableOn (by norm_num)).differentiableAt
            (hBopen.mem_nhds hζmem)
        -- evaluate both Fréchet derivatives at `e_j`
        have hL : fderiv ℝ (fun z : ℂ => PartialWord w H ((t : ℂ) * z)) ζ
              (if j = 0 then (1 : ℂ) else Complex.I)
            = (t : ℂ) * PartialWord (j :: w) H ((t : ℂ) * ζ) :=
          hfdscale (PartialWord w H) ζ hHw _
        have hR : fderiv ℝ (fun z : ℂ => ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord w (fun y : ℂ => H ((t : ℂ) * y)) z) ζ
              (if j = 0 then (1 : ℂ) else Complex.I)
            = ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord (j :: w) (fun y : ℂ => H ((t : ℂ) * y)) ζ := by
          rw [(hGw.hasFDerivAt.const_mul (((t : ℝ) : ℂ)⁻¹ ^ w.length)).fderiv]
          simp only [smul_apply, smul_eq_mul]
          rfl
        have hkey : (t : ℂ) * PartialWord (j :: w) H ((t : ℂ) * ζ)
            = ((t : ℝ) : ℂ)⁻¹ ^ w.length
                * PartialWord (j :: w) (fun y : ℂ => H ((t : ℂ) * y)) ζ := by
          rw [← hL, ← hR, hfe]
        rw [List.length_cons, pow_succ]
        refine mul_left_cancel₀ htcne ?_
        rw [hkey]
        field_simp
  exact ⟨hGa, hGb, hGc, hGd, hGe, hGf, hGg⟩
