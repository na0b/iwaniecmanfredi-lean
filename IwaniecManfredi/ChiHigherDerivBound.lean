import IwaniecManfredi.Cor1
import IwaniecManfredi.Lemma1
import IwaniecManfredi.PClassGrowthBound

/-- The estimate `|D^ν χ(z)| ≤ M|z|^{1/γ_n - l}` of Corollary 2's proof
(`paper.tex:500-508`), for every order `l` and on a punctured disk about the
origin in the `z`-plane.  Two sign facts decide the proof.  The exponent
`1 - 2l` of `J` in (49) is **negative** for `l ≥ 1`, so bounding `J^{1-2l}`
consumes the **lower** half of (42), which is where `A_{n+1} ≠ 0` is finally
used; and the conversion from `|ξ|` to `|z|` consumes **both** halves of (41),
because `1 - lγ_n` may have either sign.  The case `l = 0` is separate, since
there `χ(z) = ξ` and (49) does not apply. -/
theorem ChiHigherDerivBound (n : ℕ) (p : ℝ) (K : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (hK : 1 ≤ K)
    (V U : Set ℂ) (hV : IsOpen V) (hU : IsOpen U) (h0 : (0 : ℂ) ∈ V)
    (H chi : ℂ → ℂ)
    (hcont : ContinuousOn H V)
    (hdiff : ∀ᵐ ξ : ℂ, ξ ∈ V → DifferentiableAt ℝ H ξ)
    (hqc : QuasiconformalOn K V H)
    (h18 : SolvesEq18 n p V H)
    (hH0 : H 0 = 0)
    (hchi : ContDiffOn ℝ (⊤ : ℕ∞) chi U)
    (hmaps : ∀ ξ ∈ V \ {0}, H ξ ∈ U)
    (hinv : ∀ ξ ∈ V, chi (H ξ) = ξ) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : ℂ) δ ⊆ H '' V ∧ ∃ B : ℕ → ℝ,
      (∀ l : ℕ, 0 ≤ B l) ∧
      ∀ (l : ℕ) (w : List (Fin 2)), w.length = l →
        ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ →
          ‖PartialWord w chi z‖ ≤ B l * ‖z‖ ^ (1 / GammaExp n p - (l : ℝ)) := by
  -- ## Step 0: `γ > 0`
  have hγ : 0 < GammaExp n p := (GammaRatioMinAtOne p hp).1 n hn
  have hγne : GammaExp n p ≠ 0 := ne_of_gt hγ
  -- ## Step 1: Corollary 1
  obtain ⟨ρ, hρ, c, C, hc, hcC, Cm, hsm, h41, h42, h43, -⟩ :=
    Cor1 n p K hn hp hK V hV h0 H hcont hdiff hqc h18 hH0
  have hC : 0 < C := lt_trans hc hcC
  -- ## Step 2: the set `Ω`
  obtain ⟨Ω, hΩdef⟩ : ∃ S : Set ℂ, S = (V ∩ Metric.ball (0 : ℂ) ρ) \ {(0 : ℂ)} := ⟨_, rfl⟩
  have hΩmem : ∀ ξ : ℂ, ξ ∈ Ω ↔ (ξ ∈ V ∧ ‖ξ‖ < ρ ∧ ξ ≠ 0) := by
    intro ξ
    rw [hΩdef]
    constructor
    · intro h
      exact ⟨h.1.1, by simpa [dist_zero_right] using h.1.2, by simpa using h.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, by simpa [dist_zero_right] using h2⟩, by simpa using h3⟩
  have hΩopen : IsOpen Ω := by
    rw [hΩdef]
    exact (hV.inter Metric.isOpen_ball).sdiff isClosed_singleton
  have hΩsub : Ω ⊆ Metric.ball (0 : ℂ) ρ \ {0} := by
    intro ξ hξ
    obtain ⟨h1, h2, h3⟩ := (hΩmem ξ).mp hξ
    exact ⟨by simpa [dist_zero_right] using h2, by simpa using h3⟩
  have hHΩ : ContDiffOn ℝ (⊤ : ℕ∞) H Ω := hsm.mono hΩsub
  have hneΩ : ∀ ξ ∈ Ω, ξ ≠ 0 := fun ξ hξ => ((hΩmem ξ).mp hξ).2.2
  have hnormΩ : ∀ ξ ∈ Ω, (0 : ℝ) < ‖ξ‖ := fun ξ hξ => norm_pos_iff.mpr (hneΩ ξ hξ)
  have h41Ω : ∀ ξ ∈ Ω, c * ‖ξ‖ ^ GammaExp n p ≤ ‖H ξ‖
      ∧ ‖H ξ‖ ≤ C * ‖ξ‖ ^ GammaExp n p := by
    intro ξ hξ
    exact h41 ξ (le_of_lt ((hΩmem ξ).mp hξ).2.1)
  have h42Ω : ∀ ξ ∈ Ω, c * ‖ξ‖ ^ (2 * GammaExp n p - 2) ≤ Jac H ξ
      ∧ Jac H ξ ≤ C * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by
    intro ξ hξ
    exact h42 ξ (hnormΩ ξ hξ) (le_of_lt ((hΩmem ξ).mp hξ).2.1)
  have h43Ω : ∀ (m : ℕ), ∀ ξ ∈ Ω,
      ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        ≤ Cm m * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
    intro m ξ hξ
    exact h43 m ξ (hnormΩ ξ hξ) (le_of_lt ((hΩmem ξ).mp hξ).2.1)
  -- ## Step 3: `J > 0` on `Ω` --- this is where the lower half of (42) enters
  have hJpos : ∀ ξ ∈ Ω, 0 < Jac H ξ := by
    intro ξ hξ
    have hlow := (h42Ω ξ hξ).1
    have hx : (0 : ℝ) < c * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by
      have := hnormΩ ξ hξ
      positivity
    linarith
  have hJne : ∀ ξ ∈ Ω, Jac H ξ ≠ 0 := fun ξ hξ => ne_of_gt (hJpos ξ hξ)
  have hmapsΩ : ∀ ξ ∈ Ω, H ξ ∈ U := by
    intro ξ hξ
    obtain ⟨h1, _, h3⟩ := (hΩmem ξ).mp hξ
    exact hmaps ξ ⟨h1, by simpa using h3⟩
  have hinvΩ : ∀ ξ ∈ Ω, chi (H ξ) = ξ := fun ξ hξ => hinv ξ ((hΩmem ξ).mp hξ).1
  -- ## Steps 4-8: the per-word bound in the `ξ`-variable
  have hper : ∀ w : List (Fin 2), ∃ M : ℝ, 0 ≤ M ∧
      ∀ ξ ∈ Ω, ‖PartialWord w chi (H ξ)‖
        ≤ M * ‖ξ‖ ^ (1 - (w.length : ℝ) * GammaExp n p) := by
    intro w
    rcases w with _ | ⟨t, tl⟩
    · -- ## Step 8: the empty word, where `χ(H ξ) = ξ`
      refine ⟨1, zero_le_one, ?_⟩
      intro ξ hξ
      have h1 : PartialWord ([] : List (Fin 2)) chi (H ξ) = ξ := hinvΩ ξ hξ
      rw [h1]
      simp
    · -- ## Steps 4-7: `l = tl.length + 1 ≥ 1`
      obtain ⟨P, hP, h49⟩ := Lemma1 Ω U hΩopen hU chi H hHΩ hchi hmapsΩ hinvΩ hJne
        (tl.length + 1) (by omega) (t :: tl) (by simp)
      have hi1 : 4 * (tl.length + 1) - 3 = 4 * tl.length + 1 := by omega
      have hi2 : 3 * (tl.length + 1) - 2 = 3 * tl.length + 1 := by omega
      rw [hi1, hi2] at hP
      obtain ⟨Mw, hMw0, hMw⟩ := PClassGrowthBound H Ω hΩopen hHΩ hneΩ (GammaExp n p) Cm h43Ω
        (4 * tl.length + 1) (3 * tl.length + 1) P hP
      obtain ⟨e, he⟩ : ∃ e : ℝ, e = -1 - 2 * (tl.length : ℝ) := ⟨_, rfl⟩
      have hecast : ((1 - 2 * ((tl.length + 1 : ℕ) : ℤ) : ℤ) : ℝ) = e := by
        rw [he]; push_cast; ring
      have hene : e ≤ 0 := by
        have : (0 : ℝ) ≤ (tl.length : ℝ) := Nat.cast_nonneg _
        rw [he]; linarith
      refine ⟨c ^ e * Mw, mul_nonneg (Real.rpow_nonneg hc.le e) hMw0, ?_⟩
      intro ξ hξ
      have hx0 : (0 : ℝ) < ‖ξ‖ := hnormΩ ξ hξ
      have hJ := hJpos ξ hξ
      have hJlow := (h42Ω ξ hξ).1
      have hclow : (0 : ℝ) < c * ‖ξ‖ ^ (2 * GammaExp n p - 2) := by positivity
      have hnj : ‖((Jac H ξ : ℝ) : ℂ) ^ (1 - 2 * ((tl.length + 1 : ℕ) : ℤ))‖
          = Jac H ξ ^ e := by
        rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJ,
          ← Real.rpow_intCast (Jac H ξ) (1 - 2 * ((tl.length + 1 : ℕ) : ℤ)), hecast]
      have hA : Jac H ξ ^ e ≤ c ^ e * ‖ξ‖ ^ ((2 * GammaExp n p - 2) * e) := by
        have h1 : Jac H ξ ^ e ≤ (c * ‖ξ‖ ^ (2 * GammaExp n p - 2)) ^ e :=
          Real.rpow_le_rpow_of_nonpos hclow hJlow hene
        rw [Real.mul_rpow hc.le (Real.rpow_nonneg (norm_nonneg ξ) _),
          ← Real.rpow_mul (norm_nonneg ξ)] at h1
        exact h1
      have hB := hMw ξ hξ
      have hcombine : ‖ξ‖ ^ ((2 * GammaExp n p - 2) * e)
          * ‖ξ‖ ^ (((3 * tl.length + 1 : ℕ) : ℝ) * GammaExp n p
              - ((4 * tl.length + 1 : ℕ) : ℝ))
          = ‖ξ‖ ^ (1 - (((t :: tl).length : ℕ) : ℝ) * GammaExp n p) := by
        rw [← Real.rpow_add hx0]
        congr 1
        rw [he]
        simp only [List.length_cons]
        push_cast
        ring
      rw [h49 ξ hξ, norm_mul, hnj]
      calc Jac H ξ ^ e * ‖P ξ‖
          ≤ (c ^ e * ‖ξ‖ ^ ((2 * GammaExp n p - 2) * e))
              * (Mw * ‖ξ‖ ^ (((3 * tl.length + 1 : ℕ) : ℝ) * GammaExp n p
                  - ((4 * tl.length + 1 : ℕ) : ℝ))) :=
            mul_le_mul hA hB (norm_nonneg _) (by positivity)
        _ = c ^ e * Mw * (‖ξ‖ ^ ((2 * GammaExp n p - 2) * e)
              * ‖ξ‖ ^ (((3 * tl.length + 1 : ℕ) : ℝ) * GammaExp n p
                  - ((4 * tl.length + 1 : ℕ) : ℝ))) := by ring
        _ = c ^ e * Mw * ‖ξ‖ ^ (1 - (((t :: tl).length : ℕ) : ℝ) * GammaExp n p) := by
            rw [hcombine]
  choose Mfun hMfun0 hMfun using hper
  -- ## Step 9: the change of variable, both halves of (41)
  have hkappa : ∀ l : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ ξ ∈ Ω,
      ‖ξ‖ ^ (1 - (l : ℝ) * GammaExp n p)
        ≤ κ * ‖H ξ‖ ^ (1 / GammaExp n p - (l : ℝ)) := by
    intro l
    obtain ⟨f, hf⟩ : ∃ f : ℝ, f = 1 / GammaExp n p - (l : ℝ) := ⟨_, rfl⟩
    refine ⟨max ((c ^ f)⁻¹) ((C ^ f)⁻¹), ?_, ?_⟩
    · have h1 : (0 : ℝ) < (c ^ f)⁻¹ := by
        have := Real.rpow_pos_of_pos hc f
        positivity
      exact lt_of_lt_of_le h1 (le_max_left _ _)
    · intro ξ hξ
      have hx0 : (0 : ℝ) < ‖ξ‖ := hnormΩ ξ hξ
      have hXpos : (0 : ℝ) < ‖ξ‖ ^ GammaExp n p := Real.rpow_pos_of_pos hx0 _
      obtain ⟨hlow, hupp⟩ := h41Ω ξ hξ
      have hzpos : (0 : ℝ) < ‖H ξ‖ := by
        have : (0 : ℝ) < c * ‖ξ‖ ^ GammaExp n p := by positivity
        linarith
      have hXf : ‖ξ‖ ^ (1 - (l : ℝ) * GammaExp n p) = (‖ξ‖ ^ GammaExp n p) ^ f := by
        rw [← Real.rpow_mul (norm_nonneg ξ), hf]
        congr 1
        field_simp
      rw [hXf]
      rcases le_or_gt 0 f with hf0 | hf0
      · have h1 : ‖ξ‖ ^ GammaExp n p ≤ ‖H ξ‖ / c := by
          rw [le_div_iff₀ hc]
          linarith
        have h2 : (‖ξ‖ ^ GammaExp n p) ^ f ≤ (‖H ξ‖ / c) ^ f :=
          Real.rpow_le_rpow hXpos.le h1 hf0
        have h3 : (‖H ξ‖ / c) ^ f = (c ^ f)⁻¹ * ‖H ξ‖ ^ f := by
          rw [Real.div_rpow (norm_nonneg _) hc.le]
          ring
        rw [h3] at h2
        refine le_trans h2 ?_
        rw [hf] at *
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
      · have h1 : ‖H ξ‖ / C ≤ ‖ξ‖ ^ GammaExp n p := by
          rw [div_le_iff₀ hC]
          linarith
        have hdpos : (0 : ℝ) < ‖H ξ‖ / C := div_pos hzpos hC
        have h2 : (‖ξ‖ ^ GammaExp n p) ^ f ≤ (‖H ξ‖ / C) ^ f :=
          Real.rpow_le_rpow_of_nonpos hdpos h1 hf0.le
        have h3 : (‖H ξ‖ / C) ^ f = (C ^ f)⁻¹ * ‖H ξ‖ ^ f := by
          rw [Real.div_rpow (norm_nonneg _) hC.le]
          ring
        rw [h3] at h2
        refine le_trans h2 ?_
        rw [hf] at *
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) _)
  choose kap hkap0 hkapv using hkappa
  -- ## Step 10: the radius `δ`
  obtain ⟨-, -, -, hHVopen, psi, hpsi, hpsic⟩ := hqc
  have h0V2 : (0 : ℂ) ∈ V ∩ Metric.ball (0 : ℂ) ρ := ⟨h0, by simpa using hρ⟩
  have hV2open : IsOpen (V ∩ Metric.ball (0 : ℂ) ρ) := hV.inter Metric.isOpen_ball
  have hclaim : H '' (V ∩ Metric.ball (0 : ℂ) ρ)
      = H '' V ∩ psi ⁻¹' (V ∩ Metric.ball (0 : ℂ) ρ) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := hy
      refine ⟨⟨ξ, hξ.1, rfl⟩, ?_⟩
      rw [Set.mem_preimage, hpsi ξ hξ.1]
      exact hξ
    · intro y hy
      obtain ⟨⟨ξ, hξV, rfl⟩, hy2⟩ := hy
      rw [Set.mem_preimage, hpsi ξ hξV] at hy2
      exact ⟨ξ, hy2, rfl⟩
  have hopen : IsOpen (H '' (V ∩ Metric.ball (0 : ℂ) ρ)) := by
    rw [hclaim]
    exact hpsic.isOpen_inter_preimage hHVopen hV2open
  have hmem0 : (0 : ℂ) ∈ H '' (V ∩ Metric.ball (0 : ℂ) ρ) := ⟨0, h0V2, hH0⟩
  obtain ⟨δ, hδ0, hδsub⟩ := Metric.isOpen_iff.mp hopen 0 hmem0
  refine ⟨δ, hδ0, hδsub.trans (Set.image_mono Set.inter_subset_left), ?_⟩
  have hpre : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → ∃ ξ ∈ Ω, H ξ = z := by
    intro z hz1 hz2
    have hzb : z ∈ Metric.ball (0 : ℂ) δ := by simpa [dist_zero_right] using hz2
    obtain ⟨ξ, hξ, hξz⟩ := hδsub hzb
    refine ⟨ξ, ?_, hξz⟩
    rw [hΩmem]
    refine ⟨hξ.1, by simpa [dist_zero_right] using hξ.2, ?_⟩
    intro hc0
    rw [hc0, hH0] at hξz
    rw [← hξz] at hz1
    simp at hz1
  -- ## Step 11: the constants
  refine ⟨fun l => kap l * (∑ v : Fin l → Fin 2, Mfun (List.ofFn v)), ?_, ?_⟩
  · intro l
    refine mul_nonneg (hkap0 l).le (Finset.sum_nonneg ?_)
    intro v _
    exact hMfun0 _
  · intro l w hw z hz1 hz2
    subst hw
    obtain ⟨ξ, hξ, hξz⟩ := hpre z hz1 hz2
    have hMle : Mfun w ≤ ∑ v : Fin w.length → Fin 2, Mfun (List.ofFn v) := by
      have h := Finset.single_le_sum
        (f := fun v : Fin w.length → Fin 2 => Mfun (List.ofFn v))
        (fun v _ => hMfun0 _) (Finset.mem_univ w.get)
      rwa [List.ofFn_get w] at h
    have h1 := hMfun w ξ hξ
    have h2 := hkapv w.length ξ hξ
    rw [← hξz]
    calc ‖PartialWord w chi (H ξ)‖
        ≤ Mfun w * ‖ξ‖ ^ (1 - (w.length : ℝ) * GammaExp n p) := h1
      _ ≤ Mfun w * (kap w.length * ‖H ξ‖ ^ (1 / GammaExp n p - (w.length : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (hMfun0 w)
      _ ≤ (∑ v : Fin w.length → Fin 2, Mfun (List.ofFn v))
            * (kap w.length * ‖H ξ‖ ^ (1 / GammaExp n p - (w.length : ℝ))) := by
          refine mul_le_mul_of_nonneg_right hMle ?_
          have := (hkap0 w.length).le
          have h3 : (0 : ℝ) ≤ ‖H ξ‖ ^ (1 / GammaExp n p - (w.length : ℝ)) :=
            Real.rpow_nonneg (norm_nonneg _) _
          positivity
      _ = kap w.length * (∑ v : Fin w.length → Fin 2, Mfun (List.ofFn v))
            * ‖H ξ‖ ^ (1 / GammaExp n p - (w.length : ℝ)) := by ring
