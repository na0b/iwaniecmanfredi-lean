import IwaniecManfredi.Thm2TermSolvesEq18
set_option maxHeartbeats 1000000

/-- The all-order derivative estimate for a single summand of the series (19),
together with the smoothness of that summand off the origin.

Write `D_w` for iterated directional differentiation of a function on `ℂ`
along the letters of a word `w : List ℂ`, so `D_[] f = f` and
`D_{v :: w} f = (z ↦ df(D_w f)(z)[v])`, and write `V_w` for the product of
the norms of the letters of `w`.  Then for every word `w`, every `m` and
every `ξ ≠ 0`,
`‖D_w T_{n+m}(ξ)‖ ≤ (2((n+m)(3 + √(p-1)) + |w|))^{|w|} V_w (2‖A_{n+m}‖)
  ‖ξ‖^{λ_{n+m} - |w|}`,
and `D_w T_{n+m}` is `C^∞` at every `ξ ≠ 0`.

This is the paper's "we note that `lim λ_k = ∞`.  Therefore, we can perform
any finite number of term-by-term differentiations in formula (19)"
(`paper.tex:387`) made quantitative on one term: each differentiation lowers
the common exponent of the term by one and inflates its coefficient by a
factor `2((n+m)(3 + √(p-1)) + |w|)`, which is polynomial in `n + m` and
therefore harmless against the geometric decay `ρ^{λ_{n+m}}`.

The engine is the monomial class `E(s,j,l)(ξ) = |ξ|^s ξ^j conj(ξ)^l`: the
summand `T_{n+m}` is a two-term combination of such monomials, the class is
closed under `∂/∂ξ` and `∂/∂conj(ξ)` with the exponent total `s + j + l`
dropping by one, and the frequency bound `|s|/2 + |j| + |l|` growing by at
most one per differentiation.  No sector decomposition and no Wirtinger
bookkeeping beyond that is needed.

Both `D_w` and `V_w` are produced existentially rather than as separate
definition nodes, because only their two recursions (`D_[]`, `D_{v::w}`, and
`V_w` as the product of letter norms) are ever used. -/
theorem Thm2TermWordDerivBound (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p) (A : ℤ → ℂ) :
    ∃ Dw : List ℂ → (ℂ → ℂ) → (ℂ → ℂ), ∃ Vp : List ℂ → ℝ,
      (∀ f : ℂ → ℂ, Dw [] f = f)
      ∧ (∀ (v : ℂ) (w : List ℂ) (f : ℂ → ℂ),
          Dw (v :: w) f = fun z : ℂ => fderiv ℝ (Dw w f) z v)
      ∧ (∀ w : List ℂ, Vp w = (w.map (fun v => ‖v‖)).prod)
      ∧ (∀ (v : ℂ) (w : List ℂ), Vp (v :: w) = ‖v‖ * Vp w)
      ∧ (∀ w : List ℂ, 0 ≤ Vp w)
      ∧ (∀ (w : List ℂ) (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
          ‖Dw w (Thm2Term n p A (n + m)) ξ‖
            ≤ (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1))
                  + (w.length : ℝ))) ^ (w.length)
                * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)))
      ∧ (∀ (w : List ℂ) (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
          ContDiffAt ℝ (⊤ : ℕ∞) (Dw w (Thm2Term n p A (n + m))) ξ) := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  have hcast : ∀ m : ℕ, (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := by
    intro m; push_cast; ring
  -- `λ_{n+m} ≥ 0`, `|ε_{n+m}| ≤ 1`, `λ_{n+m} ≤ (n+m)√(p-1)`
  have hL0 : ∀ m : ℕ, 0 ≤ LambdaCoef n (n + m) p := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
    · have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
  have hepsle : ∀ m : ℕ, |EpsCoef n (n + m) p| ≤ 1 := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hepsn]; norm_num
    · exact (hepsbd (n + m) (by omega)).le
  have hLup : ∀ m : ℕ, LambdaCoef n (n + m) p ≤ ((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
      have hs : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
      have : (0 : ℝ) ≤ (n : ℝ) + ((0 : ℕ) : ℝ) := by positivity
      exact mul_nonneg this hs
    · have h2 := (hlambd (n + m) (by omega)).2
      rw [hcast m] at h2
      exact h2
  obtain ⟨EE, hEEf⟩ : ∃ EE : ℝ → ℤ → ℤ → ℂ → ℂ, ∀ (s : ℝ) (j l : ℤ),
      EE s j l = fun ξ : ℂ => ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l :=
    ⟨fun s j l ξ => ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l, fun _ _ _ => rfl⟩
  have hEEv : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ),
      EE s j l ξ = ((‖ξ‖ ^ s : ℝ) : ℂ) * ξ ^ j * (starRingEnd ℂ ξ) ^ l := by
    intro s j l ξ
    rw [hEEf s j l]
  obtain ⟨SE, hSEf⟩ : ∃ SE : ℝ → List (ℂ × ℤ × ℤ) → ℂ → ℂ,
      ∀ (s : ℝ) (L : List (ℂ × ℤ × ℤ)),
        SE s L = fun ξ : ℂ => (L.map (fun t => t.1 * EE s t.2.1 t.2.2 ξ)).sum :=
    ⟨fun s L ξ => (L.map (fun t => t.1 * EE s t.2.1 t.2.2 ξ)).sum, fun _ _ => rfl⟩
  have hSEv : ∀ (s : ℝ) (L : List (ℂ × ℤ × ℤ)) (ξ : ℂ),
      SE s L ξ = (L.map (fun t => t.1 * EE s t.2.1 t.2.2 ξ)).sum := by
    intro s L ξ
    rw [hSEf s L]
  obtain ⟨DL, hDLv⟩ : ∃ DL : ℝ → ℂ → List (ℂ × ℤ × ℤ) → List (ℂ × ℤ × ℤ),
      ∀ (s : ℝ) (v : ℂ) (L : List (ℂ × ℤ × ℤ)), DL s v L
        = L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v, t.2.1 - 1, t.2.2))
          ++ L.map (fun t =>
              (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ v),
                t.2.1, t.2.2 - 1)) :=
    ⟨fun s v L =>
      L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v, t.2.1 - 1, t.2.2))
        ++ L.map (fun t =>
            (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ v),
              t.2.1, t.2.2 - 1)), fun _ _ _ => rfl⟩
  obtain ⟨Lsum, hLsumv⟩ : ∃ Lsum : List (ℂ × ℤ × ℤ) → ℝ,
      ∀ L : List (ℂ × ℤ × ℤ), Lsum L = (L.map (fun t => ‖t.1‖)).sum :=
    ⟨fun L => (L.map (fun t => ‖t.1‖)).sum, fun _ => rfl⟩
  obtain ⟨Dw, hDwnil, hDwcons⟩ : ∃ Dw : List ℂ → (ℂ → ℂ) → (ℂ → ℂ),
      (∀ f : ℂ → ℂ, Dw [] f = f)
      ∧ ∀ (v : ℂ) (w : List ℂ) (f : ℂ → ℂ),
          Dw (v :: w) f = fun z : ℂ => fderiv ℝ (Dw w f) z v :=
    ⟨fun w f => w.foldr (fun v g => fun z => fderiv ℝ g z v) f,
      fun _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨Vp, hVpv⟩ : ∃ Vp : List ℂ → ℝ,
      ∀ w : List ℂ, Vp w = (w.map (fun v => ‖v‖)).prod :=
    ⟨fun w => (w.map (fun v => ‖v‖)).prod, fun _ => rfl⟩
  have zpowcd : ∀ (j : ℤ) (ξ : ℂ), ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => z ^ j) ξ := by
    as_aux_lemma =>
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
    as_aux_lemma =>
      intro l ξ hξ
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) ξ :=
        Complex.conjCLE.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => w ^ l) (starRingEnd ℂ ξ) :=
        zpowcd l _ (by simpa using hξ)
      exact h2.comp ξ h1
  have EEnorm : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 →
      ‖EE s j l ξ‖ = ‖ξ‖ ^ (s + (j : ℝ) + (l : ℝ)) := by
    as_aux_lemma =>
      intro s j l ξ hξ
      have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      rw [hEEv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hr s), norm_zpow, norm_zpow, Complex.norm_conj,
        ← Real.rpow_intCast ‖ξ‖ j, ← Real.rpow_intCast ‖ξ‖ l,
        ← Real.rpow_add hr, ← Real.rpow_add hr]
  have EEcd : ∀ (s : ℝ) (j l : ℤ) (ξ : ℂ), ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (EE s j l) ξ := by
    as_aux_lemma =>
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
    as_aux_lemma =>
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
  have EEfderiv : ∀ (s : ℝ) (j l : ℤ) (ξ v : ℂ), ξ ≠ 0 →
      fderiv ℝ (EE s j l) ξ v
        = ((s / 2 + (j : ℝ) : ℝ) : ℂ) * EE s (j - 1) l ξ * v
          + ((s / 2 + (l : ℝ) : ℝ) : ℂ) * EE s j (l - 1) ξ * (starRingEnd ℂ v) := by
    as_aux_lemma =>
      intro s j l ξ v hξ
      have hd : fderiv ℝ (EE s j l) ξ v
          = DZ (EE s j l) ξ * v + DZbar (EE s j l) ξ * (starRingEnd ℂ v) := by
        obtain ⟨x, y, hvv⟩ : ∃ x y : ℝ, v = (x : ℂ) + (y : ℂ) * Complex.I :=
          ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
        subst hvv
        have hsm : ((x : ℂ) + (y : ℂ) * Complex.I) = x • (1 : ℂ) + y • Complex.I := by
          rw [Complex.real_smul, Complex.real_smul, mul_one]
        have hlin : fderiv ℝ (EE s j l) ξ ((x : ℂ) + (y : ℂ) * Complex.I)
            = (x : ℂ) * fderiv ℝ (EE s j l) ξ 1 + (y : ℂ) * fderiv ℝ (EE s j l) ξ Complex.I := by
          rw [hsm, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
        have hconj : (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)
            = (x : ℂ) - (y : ℂ) * Complex.I := by
          simp [sub_eq_add_neg]
        rw [hlin, hconj, DZ, DZbar]
        linear_combination ((y : ℂ) * fderiv ℝ (EE s j l) ξ Complex.I) * Complex.I_sq
      rw [hd, (EEDZ s j l ξ hξ).1, (EEDZ s j l ξ hξ).2]
  have SEnil : ∀ s : ℝ, SE s [] = fun _ : ℂ => 0 := by
    as_aux_lemma =>
      intro s
      rw [hSEf s []]
      funext z
      simp
  have SEcons : ∀ (s : ℝ) (t : ℂ × ℤ × ℤ) (L : List (ℂ × ℤ × ℤ)) (ξ : ℂ),
      SE s (t :: L) ξ = t.1 * EE s t.2.1 t.2.2 ξ + SE s L ξ := by
    as_aux_lemma =>
      intro s t L ξ
      rw [hSEv, hSEv]
      simp
  have SEappend : ∀ (s : ℝ) (L1 L2 : List (ℂ × ℤ × ℤ)) (ξ : ℂ),
      SE s (L1 ++ L2) ξ = SE s L1 ξ + SE s L2 ξ := by
    as_aux_lemma =>
      intro s L1 L2 ξ
      rw [hSEv, hSEv, hSEv]
      simp [List.map_append, List.sum_append]
  have SEcd : ∀ (s : ℝ) (L : List (ℂ × ℤ × ℤ)) (ξ : ℂ), ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (SE s L) ξ := by
    as_aux_lemma =>
      intro s L ξ hξ
      induction L with
      | nil => rw [SEnil]; exact contDiffAt_const
      | cons t L ih =>
          have hfe : SE s (t :: L) = fun z : ℂ => t.1 * EE s t.2.1 t.2.2 z + SE s L z := by
            funext z; exact SEcons s t L z
          rw [hfe]
          exact (contDiffAt_const.mul (EEcd s t.2.1 t.2.2 ξ hξ)).add ih
  have SEdiff : ∀ (s : ℝ) (L : List (ℂ × ℤ × ℤ)) (ξ : ℂ), ξ ≠ 0 →
      DifferentiableAt ℝ (SE s L) ξ :=
    fun s L ξ hξ => (SEcd s L ξ hξ).differentiableAt (by simp)
  have SEfderiv : ∀ (s : ℝ) (L : List (ℂ × ℤ × ℤ)) (ξ v : ℂ), ξ ≠ 0 →
      fderiv ℝ (SE s L) ξ v = SE s (DL s v L) ξ := by
    as_aux_lemma =>
      intro s L ξ v hξ
      induction L with
      | nil =>
          rw [SEnil]
          simp [hDLv, hSEv]
      | cons t L ih =>
          have hfe : SE s (t :: L) = fun z : ℂ => t.1 * EE s t.2.1 t.2.2 z + SE s L z := by
            funext z; exact SEcons s t L z
          have h1 : HasFDerivAt (fun z : ℂ => t.1 * EE s t.2.1 t.2.2 z)
              (t.1 • fderiv ℝ (EE s t.2.1 t.2.2) ξ) ξ :=
            (EEdiff s t.2.1 t.2.2 ξ hξ).hasFDerivAt.const_mul t.1
          have h2 : HasFDerivAt (SE s L) (fderiv ℝ (SE s L) ξ) ξ := (SEdiff s L ξ hξ).hasFDerivAt
          have hDLc : DL s v (t :: L)
              = (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v, t.2.1 - 1, t.2.2)
                :: ((L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v,
                      t.2.1 - 1, t.2.2)))
                  ++ ((t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ v),
                        t.2.1, t.2.2 - 1)
                    :: L.map (fun t => (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ)
                        * (starRingEnd ℂ v), t.2.1, t.2.2 - 1)))) := by
            simp [hDLv, List.cons_append]
          have hIH : fderiv ℝ (SE s L) ξ v
              = SE s (L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v,
                    t.2.1 - 1, t.2.2))) ξ
                + SE s (L.map (fun t => (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ)
                    * (starRingEnd ℂ v), t.2.1, t.2.2 - 1))) ξ := by
            rw [ih, hDLv, SEappend]
          rw [hfe, (h1.fun_add h2).fderiv]
          simp only [add_apply, smul_apply, smul_eq_mul]
          rw [EEfderiv s t.2.1 t.2.2 ξ v hξ, hIH, hDLc, SEcons, SEappend, SEcons]
          ring
  have Lsumnil : Lsum [] = 0 := by rw [hLsumv]; simp
  have Lsumcons : ∀ (t : ℂ × ℤ × ℤ) (L : List (ℂ × ℤ × ℤ)), Lsum (t :: L) = ‖t.1‖ + Lsum L := by
    as_aux_lemma =>
      intro t L
      rw [hLsumv, hLsumv]
      simp
  have Lsumappend : ∀ L1 L2 : List (ℂ × ℤ × ℤ), Lsum (L1 ++ L2) = Lsum L1 + Lsum L2 := by
    as_aux_lemma =>
      intro L1 L2
      rw [hLsumv, hLsumv, hLsumv]
      simp [List.map_append, List.sum_append]
  have Lsumnonneg : ∀ L : List (ℂ × ℤ × ℤ), 0 ≤ Lsum L := by
    as_aux_lemma =>
      intro L
      induction L with
      | nil => rw [Lsumnil]
      | cons t L ih => rw [Lsumcons]; have := norm_nonneg t.1; linarith
  have SEnormle : ∀ (s e : ℝ) (L : List (ℂ × ℤ × ℤ)) (ξ : ℂ), ξ ≠ 0 →
      (∀ t ∈ L, s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = e) →
      ‖SE s L ξ‖ ≤ Lsum L * ‖ξ‖ ^ e := by
    as_aux_lemma =>
      intro s e L ξ hξ h
      have hpw : (0 : ℝ) ≤ ‖ξ‖ ^ e := Real.rpow_nonneg (norm_nonneg _) _
      induction L with
      | nil =>
          rw [SEnil, Lsumnil]
          simp
      | cons t L ih =>
          rw [SEcons, Lsumcons]
          have h1 : ‖t.1 * EE s t.2.1 t.2.2 ξ‖ = ‖t.1‖ * ‖ξ‖ ^ e := by
            rw [norm_mul, EEnorm s t.2.1 t.2.2 ξ hξ, h t (by simp)]
          have h2 := ih (fun u hu => h u (by simp [hu]))
          calc ‖t.1 * EE s t.2.1 t.2.2 ξ + SE s L ξ‖
              ≤ ‖t.1 * EE s t.2.1 t.2.2 ξ‖ + ‖SE s L ξ‖ := norm_add_le _ _
            _ ≤ ‖t.1‖ * ‖ξ‖ ^ e + Lsum L * ‖ξ‖ ^ e := by rw [h1] at *; linarith
            _ = (‖t.1‖ + Lsum L) * ‖ξ‖ ^ e := by ring
  have DLexp : ∀ (s e : ℝ) (v : ℂ) (L : List (ℂ × ℤ × ℤ)),
      (∀ t ∈ L, s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = e) →
      ∀ t ∈ DL s v L, s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = e - 1 := by
    as_aux_lemma =>
      intro s e v L h t ht
      rw [hDLv, List.mem_append] at ht
      rcases ht with ht | ht
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        have hh := h u hu
        push_cast
        linarith
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        have hh := h u hu
        push_cast
        linarith
  have DLfreq : ∀ (s K : ℝ) (v : ℂ) (L : List (ℂ × ℤ × ℤ)),
      (∀ t ∈ L, |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K) →
      ∀ t ∈ DL s v L, |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K + 1 := by
    as_aux_lemma =>
      intro s K v L h t ht
      rw [hDLv, List.mem_append] at ht
      rcases ht with ht | ht
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        have hh := h u hu
        have hab : |((u.2.1 : ℝ) - 1)| ≤ |(u.2.1 : ℝ)| + 1 := by
          have := abs_sub_abs_le_abs_sub ((u.2.1 : ℝ)) 1
          have h2 : |(1 : ℝ)| = 1 := abs_one
          have := abs_sub ((u.2.1 : ℝ)) (1 : ℝ)
          calc |((u.2.1 : ℝ) - 1)| ≤ |(u.2.1 : ℝ)| + |(1 : ℝ)| := abs_sub _ _
            _ = |(u.2.1 : ℝ)| + 1 := by rw [h2]
        show |s| / 2 + |((u.2.1 - 1 : ℤ) : ℝ)| + |((u.2.2 : ℤ) : ℝ)| ≤ K + 1
        push_cast
        linarith
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        have hh := h u hu
        have hab : |((u.2.2 : ℝ) - 1)| ≤ |(u.2.2 : ℝ)| + 1 := by
          have h2 : |(1 : ℝ)| = 1 := abs_one
          calc |((u.2.2 : ℝ) - 1)| ≤ |(u.2.2 : ℝ)| + |(1 : ℝ)| := abs_sub _ _
            _ = |(u.2.2 : ℝ)| + 1 := by rw [h2]
        show |s| / 2 + |((u.2.1 : ℤ) : ℝ)| + |((u.2.2 - 1 : ℤ) : ℝ)| ≤ K + 1
        push_cast
        linarith
  have DLbound : ∀ (s K : ℝ) (v : ℂ) (L : List (ℂ × ℤ × ℤ)), 0 ≤ K →
      (∀ t ∈ L, |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K) →
      Lsum (DL s v L) ≤ 2 * K * ‖v‖ * Lsum L := by
    as_aux_lemma =>
      intro s K v L hK h
      induction L with
      | nil => rw [hDLv]; simp [Lsumnil]
      | cons t L ih =>
          have hDLc : DL s v (t :: L)
              = (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v, t.2.1 - 1, t.2.2)
                :: ((L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v,
                      t.2.1 - 1, t.2.2)))
                  ++ ((t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ v),
                        t.2.1, t.2.2 - 1)
                    :: L.map (fun t => (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ)
                        * (starRingEnd ℂ v), t.2.1, t.2.2 - 1)))) := by
            simp [hDLv, List.cons_append]
          have hIH : Lsum (DL s v L)
              = Lsum (L.map (fun t => (t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v,
                    t.2.1 - 1, t.2.2)))
                + Lsum (L.map (fun t => (t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ)
                    * (starRingEnd ℂ v), t.2.1, t.2.2 - 1))) := by
            rw [hDLv, Lsumappend]
          have hb := ih (fun u hu => h u (by simp [hu]))
          rw [hIH] at hb
          have ht := h t (by simp)
          have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
          have hc1 : ‖t.1 * ((s / 2 + (t.2.1 : ℝ) : ℝ) : ℂ) * v‖ ≤ ‖t.1‖ * K * ‖v‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have h1 : |s / 2 + (t.2.1 : ℝ)| ≤ K := by

              have h2 : |s / 2| = |s| / 2 := by
                rw [abs_div]
                norm_num
              have h3 : (0 : ℝ) ≤ |(t.2.2 : ℝ)| := abs_nonneg _
              calc |s / 2 + (t.2.1 : ℝ)| ≤ |s / 2| + |(t.2.1 : ℝ)| := abs_add_le _ _
                _ = |s| / 2 + |(t.2.1 : ℝ)| := by rw [h2]
                _ ≤ K := by linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (norm_nonneg t.1)) hv0
          have hc2 : ‖t.1 * ((s / 2 + (t.2.2 : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ v)‖
              ≤ ‖t.1‖ * K * ‖v‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
            have h1 : |s / 2 + (t.2.2 : ℝ)| ≤ K := by
              have h2 : |s / 2| = |s| / 2 := by
                rw [abs_div]
                norm_num
              have h3 : (0 : ℝ) ≤ |(t.2.1 : ℝ)| := abs_nonneg _
              calc |s / 2 + (t.2.2 : ℝ)| ≤ |s / 2| + |(t.2.2 : ℝ)| := abs_add_le _ _
                _ = |s| / 2 + |(t.2.2 : ℝ)| := by rw [h2]
                _ ≤ K := by linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (norm_nonneg t.1)) hv0
          rw [hDLc, Lsumcons, Lsumappend, Lsumcons, Lsumcons]
          linarith
  have Vpnonneg : ∀ w : List ℂ, 0 ≤ Vp w := by
    as_aux_lemma =>
      intro w
      induction w with
      | nil => rw [hVpv]; simp
      | cons v w ih =>
          rw [hVpv, List.map_cons, List.prod_cons]
          rw [hVpv] at ih
          exact mul_nonneg (norm_nonneg v) ih
  have Vpcons : ∀ (v : ℂ) (w : List ℂ), Vp (v :: w) = ‖v‖ * Vp w := by
    as_aux_lemma =>
      intro v w
      rw [hVpv, hVpv, List.map_cons, List.prod_cons]
  have hkey : ∀ (w : List ℂ) (s e K : ℝ) (L : List (ℂ × ℤ × ℤ)), 0 ≤ K →
      (∀ t ∈ L, s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = e) →
      (∀ t ∈ L, |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K) →
      ∃ L' : List (ℂ × ℤ × ℤ),
        (∀ ξ : ℂ, ξ ≠ 0 → Dw w (SE s L) ξ = SE s L' ξ)
        ∧ (∀ t ∈ L', s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = e - (w.length : ℝ))
        ∧ (∀ t ∈ L', |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K + (w.length : ℝ))
        ∧ Lsum L' ≤ (2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * Lsum L := by
    as_aux_lemma =>
      intro w
      induction w with
      | nil =>
          intro s e K L hK he hf
          refine ⟨L, fun ξ _ => by rw [hDwnil], ?_, ?_, ?_⟩
          · intro t ht; have := he t ht; simp; linarith
          · intro t ht; have := hf t ht; simp; linarith
          · rw [hVpv]; simp
      | cons v w ih =>
          intro s e K L hK he hf
          obtain ⟨L₁, h1, h2, h3, h4⟩ := ih s e K L hK he hf
          refine ⟨DL s v L₁, ?_, ?_, ?_, ?_⟩
          · intro ξ hξ
            rw [hDwcons]
            have hfe : fderiv ℝ (Dw w (SE s L)) ξ = fderiv ℝ (SE s L₁) ξ :=
              Filter.EventuallyEq.fderiv_eq
                (Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hξ) (fun z hz => h1 z hz))
            show fderiv ℝ (Dw w (SE s L)) ξ v = SE s (DL s v L₁) ξ
            rw [hfe, SEfderiv s L₁ ξ v hξ]
          · intro t ht
            have := DLexp s (e - (w.length : ℝ)) v L₁ h2 t ht
            have hl : (((v :: w).length : ℕ) : ℝ) = (w.length : ℝ) + 1 := by
              simp
            rw [hl]
            linarith
          · intro t ht
            have := DLfreq s (K + (w.length : ℝ)) v L₁ h3 t ht
            have hl : (((v :: w).length : ℕ) : ℝ) = (w.length : ℝ) + 1 := by
              simp
            rw [hl]
            linarith
          · have hKM : (0 : ℝ) ≤ K + (w.length : ℝ) := by positivity
            have hb := DLbound s (K + (w.length : ℝ)) v L₁ hKM h3
            have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
            have hc0 : (0 : ℝ) ≤ 2 * (K + (w.length : ℝ)) * ‖v‖ := by positivity
            have hL0 : (0 : ℝ) ≤ Lsum L := Lsumnonneg L
            have hVp : (0 : ℝ) ≤ Vp w := Vpnonneg w
            have hbase : (0 : ℝ) ≤ 2 * (K + (w.length : ℝ)) := by positivity
            have hmono : (2 * (K + (w.length : ℝ))) ^ (w.length + 1)
                ≤ (2 * (K + ((w.length : ℝ) + 1))) ^ (w.length + 1) :=
              pow_le_pow_left₀ hbase (by linarith) _
            have hl : (((v :: w).length : ℕ) : ℝ) = (w.length : ℝ) + 1 := by simp
            have hlen : (v :: w).length = w.length + 1 := by simp
            rw [hl, hlen, Vpcons]
            calc Lsum (DL s v L₁)
                ≤ 2 * (K + (w.length : ℝ)) * ‖v‖ * Lsum L₁ := hb
              _ ≤ 2 * (K + (w.length : ℝ)) * ‖v‖
                    * ((2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * Lsum L) :=
                  mul_le_mul_of_nonneg_left h4 hc0
              _ = (2 * (K + (w.length : ℝ))) ^ (w.length + 1) * (‖v‖ * Vp w * Lsum L) := by
                  ring
              _ ≤ (2 * (K + ((w.length : ℝ) + 1))) ^ (w.length + 1) * (‖v‖ * Vp w * Lsum L) :=
                  mul_le_mul_of_nonneg_right hmono (by positivity)
              _ = (2 * (K + ((w.length : ℝ) + 1))) ^ (w.length + 1) * (‖v‖ * Vp w) * Lsum L := by
                  ring
  have Dwcongr : ∀ (w : List ℂ) (f g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → f z = g z) →
      ∀ z : ℂ, z ≠ 0 → Dw w f z = Dw w g z := by
    as_aux_lemma =>
      intro w
      induction w with
      | nil => intro f g h z hz; rw [hDwnil, hDwnil]; exact h z hz
      | cons v w ih =>
          intro f g h z hz
          rw [hDwcons, hDwcons]
          show fderiv ℝ (Dw w f) z v = fderiv ℝ (Dw w g) z v
          have he : fderiv ℝ (Dw w f) z = fderiv ℝ (Dw w g) z :=
            Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hz)
              (fun y hy => ih f g h y hy))
          rw [he]
  have Trep : ∀ (w : List ℂ) (m : ℕ), ∃ L' : List (ℂ × ℤ × ℤ),
      (∀ ξ : ℂ, ξ ≠ 0 → Dw w (Thm2Term n p A (n + m)) ξ
        = SE (LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ)) L' ξ)
      ∧ (∀ ξ : ℂ, ξ ≠ 0 →
        ‖Dw w (Thm2Term n p A (n + m)) ξ‖
          ≤ (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1))
                + (w.length : ℝ))) ^ (w.length)
              * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
            * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))) := by
    as_aux_lemma =>
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) ≤ Real.sqrt (p - 1) := Real.sqrt_nonneg _
      have hcast : ∀ m : ℕ, (((n + m : ℕ)) : ℝ) = (n : ℝ) + (m : ℝ) := by
        intro m; push_cast; ring
      have hcastA : ∀ m : ℕ, A (((n + m : ℕ)) : ℤ) = A ((n : ℤ) + (m : ℤ)) := by
        intro m; congr 1
      intro w m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      set s : ℝ := LambdaCoef n (n + m) p + (n : ℝ) - (((n + m : ℕ)) : ℝ) with hs
      set K : ℝ := ((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) with hK
      set Lk : List (ℂ × ℤ × ℤ) :=
        [(A (((n + m : ℕ)) : ℤ), (m : ℤ), (0 : ℤ)),
         (((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A (((n + m : ℕ)) : ℤ)),
            -(n : ℤ), (((n + m : ℕ)) : ℤ))] with hLk
      have hXs : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) := by positivity
      have hK0 : 0 ≤ K := by rw [hK]; positivity
      have hLu := hLup m
      have hL0m := hL0 m
      have hKexp : K = 3 * ((n : ℝ) + (m : ℝ)) + ((n : ℝ) + (m : ℝ)) * Real.sqrt (p - 1) := by
        rw [hK]; ring
      have hsabs : |s| ≤ LambdaCoef n (n + m) p + (m : ℝ) := by
        rw [hs, hcast m]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hexp : ∀ t ∈ Lk, s + (t.2.1 : ℝ) + (t.2.2 : ℝ) = LambdaCoef n (n + m) p := by
        intro t ht
        rw [hLk] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · rw [hs, hcast m]
          push_cast
          ring
        · rw [hs, hcast m]
          push_cast
          ring
      have hfreq : ∀ t ∈ Lk, |s| / 2 + |(t.2.1 : ℝ)| + |(t.2.2 : ℝ)| ≤ K := by
        intro t ht
        rw [hLk] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · push_cast
          rw [abs_of_nonneg hm0, abs_zero, hKexp]
          linarith
        · push_cast
          rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ)),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ)), hKexp]
          linarith
      have hLsum : Lsum Lk ≤ 2 * ‖A ((n : ℤ) + (m : ℤ))‖ := by
        rw [hLk, Lsumcons, Lsumcons, Lsumnil, hcastA m]
        have h1 : ‖((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A ((n : ℤ) + (m : ℤ)))‖
            ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
          have h2 := hepsle m
          have h3 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
          calc |EpsCoef n (n + m) p| * ‖A ((n : ℤ) + (m : ℤ))‖
              ≤ 1 * ‖A ((n : ℤ) + (m : ℤ))‖ := mul_le_mul_of_nonneg_right h2 h3
            _ = ‖A ((n : ℤ) + (m : ℤ))‖ := one_mul _
        simp only [add_zero]
        linarith
      obtain ⟨L', hL1, hL2, hL3, hL4⟩ := hkey w s (LambdaCoef n (n + m) p) K Lk hK0 hexp hfreq
      have hrep : ∀ z : ℂ, z ≠ 0 → Thm2Term n p A (n + m) z = SE s Lk z := by
        intro z hz
        have hcj : starRingEnd ℂ z ≠ 0 := by simpa using hz
        rw [hLk, SEcons, SEcons, SEnil, hEEv, hEEv, Thm2Term, hs]
        rw [zpow_neg, zpow_zero, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]
        field_simp
        ring
      have heq : ∀ ξ : ℂ, ξ ≠ 0 → Dw w (Thm2Term n p A (n + m)) ξ = SE s L' ξ := by
        intro ξ hξ
        rw [Dwcongr w _ (SE s Lk) hrep ξ hξ, hL1 ξ hξ]
      refine ⟨L', heq, ?_⟩
      intro ξ hξ
      rw [heq ξ hξ]
      have hpw : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hstep := SEnormle s (LambdaCoef n (n + m) p - (w.length : ℝ)) L' ξ hξ hL2
      have hVp : (0 : ℝ) ≤ Vp w := Vpnonneg w
      have hcc : (0 : ℝ) ≤ (2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w := by
        have h0 : (0 : ℝ) ≤ 2 * (K + (w.length : ℝ)) := by positivity
        positivity
      have hfin : Lsum L'
          ≤ (2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖) := by
        have h1 : (2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * Lsum Lk
            ≤ (2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖) :=
          mul_le_mul_of_nonneg_left hLsum hcc
        exact le_trans hL4 h1
      calc ‖SE s L' ξ‖ ≤ Lsum L' * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) := hstep
        _ ≤ ((2 * (K + (w.length : ℝ))) ^ (w.length) * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
              * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) :=
            mul_le_mul_of_nonneg_right hfin hpw
  -- package the two escaping facts: the bound alone (the representation by
  -- `SE` is never needed outside this node), and smoothness off the origin
  have Trepbd : ∀ (w : List ℂ) (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ‖Dw w (Thm2Term n p A (n + m)) ξ‖
        ≤ (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1))
              + (w.length : ℝ))) ^ (w.length)
            * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
          * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) := by
    intro w m ξ hξ
    obtain ⟨L', -, hb⟩ := Trep w m
    exact hb ξ hξ
  have hTcd : ∀ (w : List ℂ) (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (Dw w (Thm2Term n p A (n + m))) ξ := by
    as_aux_lemma =>
      intro w m ξ hξ
      obtain ⟨L', h1, h2⟩ := Trep w m
      exact (SEcd _ L' ξ hξ).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hξ) (fun z hz => h1 z hz))
  exact ⟨Dw, Vp, hDwnil, hDwcons, hVpv, Vpcons, Vpnonneg, Trepbd, hTcd⟩
