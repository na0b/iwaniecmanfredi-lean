import IwaniecManfredi.PClass
import IwaniecManfredi.Jac
import IwaniecManfredi.PartialWord
import IwaniecManfredi.WirtingerConjRule
import IwaniecManfredi.WirtingerProductRule
import IwaniecManfredi.WirtingerChainRule
import IwaniecManfredi.WirtingerPowerRule
import IwaniecManfredi.PClassMulClosed
import IwaniecManfredi.PClassDerivClosed
import IwaniecManfredi.PClassConjClosed
import IwaniecManfredi.PClassSmooth
import IwaniecManfredi.JacInPClass
import IwaniecManfredi.ChiFirstDerivs

/-- Lemma 1 of the paper (formula (47)): for a partial derivative operator
`D^w` of order `m ≥ 1` there is `P = P_w ∈ ℙ(4m-3, 3m-2)` with
`D^w χ(z) = J(ξ)^{1-2m} P_w(ξ)`, where `z = H(ξ)` and `χ` is inverse to `H`.
The standing assumptions of Sections 3 and 5 -- `H` smooth on the punctured
disk, `χ` smooth on its image, `χ ∘ H = id`, `J ≠ 0` -- are carried as
explicit hypotheses. -/
theorem Lemma1 (Ω U : Set ℂ) (hΩ : IsOpen Ω) (hU : IsOpen U) (chi H : ℂ → ℂ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω) (hchi : ContDiffOn ℝ (⊤ : ℕ∞) chi U)
    (hmaps : ∀ ξ ∈ Ω, H ξ ∈ U) (hinv : ∀ ξ ∈ Ω, chi (H ξ) = ξ)
    (hJ : ∀ ξ ∈ Ω, Jac H ξ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (w : List (Fin 2)) (hw : w.length = m) :
    ∃ P : ℂ → ℂ, PClass H (4 * m - 3) (3 * m - 2) P ∧
      ∀ ξ ∈ Ω, PartialWord w chi (H ξ)
        = ((Jac H ξ : ℝ) : ℂ) ^ (1 - 2 * (m : ℤ)) * P ξ := by
  -- ## Step 0 (0a): `ℙ(s,k)` is a `ℂ`-linear space
  have hPadd : ∀ (s k : ℕ) (P Q : ℂ → ℂ), PClass H s k P → PClass H s k Q →
      PClass H s k (fun ξ => P ξ + Q ξ) := by
    intro s k P Q hP hQ
    obtain ⟨LP, hPdeg, hPval⟩ := hP
    obtain ⟨LQ, hQdeg, hQval⟩ := hQ
    refine ⟨LP ++ LQ, ?_, ?_⟩
    · intro cm hcm
      rcases List.mem_append.mp hcm with h | h
      · exact hPdeg cm h
      · exact hQdeg cm h
    · intro ξ
      show P ξ + Q ξ = _
      rw [hPval ξ, hQval ξ, List.map_append, List.sum_append]
  have hPsmul : ∀ (s k : ℕ) (c : ℂ) (P : ℂ → ℂ), PClass H s k P →
      PClass H s k (fun ξ => c * P ξ) := by
    intro s k c P hP
    obtain ⟨LP, hPdeg, hPval⟩ := hP
    refine ⟨LP.map (fun cm => (c * cm.1, cm.2)), ?_, ?_⟩
    · intro cm hcm
      obtain ⟨cm0, hcm0, rfl⟩ := List.mem_map.mp hcm
      exact hPdeg cm0 hcm0
    · intro ξ
      show c * P ξ = _
      rw [hPval ξ, List.map_map]
      have hh : ((fun cm : ℂ × List DerivSymbol => cm.1 * MonomialValue H cm.2 ξ)
            ∘ (fun cm : ℂ × List DerivSymbol => (c * cm.1, cm.2)))
          = fun cm : ℂ × List DerivSymbol => c * (cm.1 * MonomialValue H cm.2 ξ) := by
        funext cm
        simp only [Function.comp_apply]
        ring
      rw [hh, List.sum_map_mul_left]
  have hPlin : ∀ (s k : ℕ) (c d : ℂ) (P Q : ℂ → ℂ), PClass H s k P → PClass H s k Q →
      PClass H s k (fun ξ => c * P ξ + d * Q ξ) := by
    intro s k c d P Q hP hQ
    exact hPadd s k _ _ (hPsmul s k c P hP) (hPsmul s k d Q hQ)
  have hPsub : ∀ (s k : ℕ) (P Q : ℂ → ℂ), PClass H s k P → PClass H s k Q →
      PClass H s k (fun ξ => P ξ - Q ξ) := by
    intro s k P Q hP hQ
    have h := hPadd s k P (fun ξ => (-1 : ℂ) * Q ξ) hP (hPsmul s k (-1) Q hQ)
    have hfe : (fun ξ => P ξ - Q ξ) = fun ξ => P ξ + (-1 : ℂ) * Q ξ := by
      funext ξ
      ring
    rw [hfe]
    exact h
  have hPcongr : ∀ (s k s' k' : ℕ) (P : ℂ → ℂ), s = s' → k = k' →
      PClass H s k P → PClass H s' k' P := by
    intro s k s' k' P hs hk hP
    rw [← hs, ← hk]
    exact hP
  have hPmul3 : ∀ (s1 k1 s2 k2 s3 k3 : ℕ) (P Q S : ℂ → ℂ),
      PClass H s1 k1 P → PClass H s2 k2 Q → PClass H s3 k3 S →
      PClass H (s1 + s2 + s3) (k1 + k2 + k3) (fun ξ => P ξ * Q ξ * S ξ) := by
    intro s1 k1 s2 k2 s3 k3 P Q S h1 h2 h3
    exact PClassMulClosed H (s1 + s2) (k1 + k2) s3 k3 _ _
      (PClassMulClosed H s1 k1 s2 k2 P Q h1 h2) h3
  -- ## Step 0 (0b): the four first-order factors lie in `ℙ(1,1)`
  have hp11 : ∀ d : DerivSymbol, d.i + d.j = 1 → PClass H 1 1 (SymbolValue H d) := by
    intro d hd
    refine ⟨[((1 : ℂ), [d])], ?_, ?_⟩
    · intro cm hcm
      simp only [List.mem_singleton] at hcm
      subst hcm
      exact ⟨by simpa using hd, by simp⟩
    · intro ξ
      simp [MonomialValue]
  have hPA : PClass H 1 1 (DZ H) := hp11 ⟨1, 0, false, by omega⟩ (by simp)
  have hPB : PClass H 1 1 (DZbar H) := hp11 ⟨0, 1, false, by omega⟩ (by simp)
  have hPAc : PClass H 1 1 (fun ξ => starRingEnd ℂ (DZ H ξ)) :=
    hp11 ⟨1, 0, true, by omega⟩ (by simp)
  have hPBc : PClass H 1 1 (fun ξ => starRingEnd ℂ (DZbar H ξ)) :=
    hp11 ⟨0, 1, true, by omega⟩ (by simp)
  -- ## Step 0 (0c): the Jacobian
  obtain ⟨Jc, hJcdef⟩ : ∃ f : ℂ → ℂ, f = fun ζ => ((Jac H ζ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hJcpt : ∀ ζ : ℂ, Jc ζ = ((Jac H ζ : ℝ) : ℂ) := by
    intro ζ; rw [hJcdef]
  have hmc : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hdet : ∀ ζ : ℂ, Jc ζ = DZ H ζ * starRingEnd ℂ (DZ H ζ)
      - DZbar H ζ * starRingEnd ℂ (DZbar H ζ) := by
    intro ζ
    rw [hmc, hmc, hJcpt, Jac]
    push_cast
    ring
  have hjac := JacInPClass H Ω hΩ hH
  have hJ22 : PClass H 2 2 Jc := by rw [hJcdef]; exact hjac.1
  obtain ⟨R, hR32, hDZJc⟩ : ∃ R : ℂ → ℂ, PClass H 3 2 R ∧ ∀ ξ ∈ Ω, DZ Jc ξ = R ξ := by
    refine ⟨_, hjac.2.1, ?_⟩
    rw [hJcdef]
    exact hjac.2.2
  have hRc32 : PClass H 3 2 (fun ξ => starRingEnd ℂ (R ξ)) := PClassConjClosed H 3 2 R hR32
  have hJsm : ContDiffOn ℝ (⊤ : ℕ∞) Jc Ω := PClassSmooth H Ω hΩ hH 2 2 Jc hJ22
  have hJcne : ∀ ξ ∈ Ω, Jc ξ ≠ 0 := by
    intro ξ hξ
    rw [hJcpt]
    exact Complex.ofReal_ne_zero.mpr (hJ ξ hξ)
  have hJcd : ∀ ξ ∈ Ω, DifferentiableAt ℝ Jc ξ := fun ξ hξ =>
    (hJsm.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ)
  have hJcreal : (fun z => starRingEnd ℂ (Jc z)) = Jc := by
    rw [hJcdef]
    funext ζ
    simp
  have hDZbarJc : ∀ ξ ∈ Ω, DZbar Jc ξ = starRingEnd ℂ (R ξ) := by
    intro ξ hξ
    have hcr := (WirtingerConjRule Jc ξ (hJcd ξ hξ)).2
    rw [hJcreal] at hcr
    rw [hcr, hDZJc ξ hξ]
  -- ## Step 0 (0d): every word derivative of `chi` is `C^∞` on `U`
  have hpwnil : ∀ (f : ℂ → ℂ) (z : ℂ), PartialWord [] f z = f z := fun _ _ => rfl
  have hpwcons : ∀ (j : Fin 2) (t : List (Fin 2)) (f : ℂ → ℂ) (z : ℂ),
      PartialWord (j :: t) f z
        = fderiv ℝ (PartialWord t f) z (if j = 0 then 1 else Complex.I) :=
    fun _ _ _ _ => rfl
  have hpwconsf : ∀ (j : Fin 2) (t : List (Fin 2)) (f : ℂ → ℂ),
      PartialWord (j :: t) f
        = fun z => fderiv ℝ (PartialWord t f) z (if j = 0 then 1 else Complex.I) :=
    fun _ _ _ => rfl
  have hpw0 : PartialWord ([] : List (Fin 2)) chi = chi := rfl
  have hchid : ∀ v : List (Fin 2), ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord v chi) U := by
    intro v
    induction v with
    | nil => exact hchi
    | cons j t ih =>
        have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ (PartialWord t chi) z) U :=
          ih.fderiv_of_isOpen hU (by simp)
        rw [hpwconsf]
        exact hfd.clm_apply contDiffOn_const
  have hHd : ∀ ξ ∈ Ω, DifferentiableAt ℝ H ξ := fun ξ hξ =>
    (hH.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hξ)
  have hFd : ∀ (v : List (Fin 2)) (ζ : ℂ), ζ ∈ U → DifferentiableAt ℝ (PartialWord v chi) ζ :=
    fun v ζ hζ => ((hchid v).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hζ)
  -- ## Step 0 (0e): the two real partials through the Wirtinger operators
  have he0 : ∀ (F : ℂ → ℂ) (ζ : ℂ), fderiv ℝ F ζ 1 = DZ F ζ + DZbar F ζ := by
    intro F ζ
    rw [DZ, DZbar]
    ring
  have he1 : ∀ (F : ℂ → ℂ) (ζ : ℂ),
      fderiv ℝ F ζ Complex.I = Complex.I * (DZ F ζ - DZbar F ζ) := by
    intro F ζ
    rw [DZ, DZbar]
    linear_combination (fderiv ℝ F ζ Complex.I) * Complex.I_mul_I
  -- ## The induction, stated with untruncated indices
  have main : ∀ (M : ℕ) (v : List (Fin 2)), v.length = M + 1 →
      ∃ P : ℂ → ℂ, PClass H (4 * M + 1) (3 * M + 1) P ∧
        ∀ ξ ∈ Ω, PartialWord v chi (H ξ) = Jc ξ ^ (-1 - 2 * (M : ℤ)) * P ξ := by
    intro M
    induction M with
    | zero =>
        -- ## Step 1: the base case
        intro v hv
        obtain ⟨j, rfl⟩ : ∃ j : Fin 2, v = [j] := List.length_eq_one_iff.mp (by simpa using hv)
        have hbase : ∀ ξ ∈ Ω, DZ chi (H ξ) = starRingEnd ℂ (DZ H ξ) / Jc ξ ∧
            DZbar chi (H ξ) = -(DZbar H ξ) / Jc ξ := by
          intro ξ hξ
          have := ChiFirstDerivs Ω hΩ chi H ξ hξ hinv (hHd ξ hξ)
            (hFd [] (H ξ) (hmaps ξ hξ)) (hJ ξ hξ)
          rw [hJcpt]
          exact this
        have hexp0 : ∀ ξ ∈ Ω, Jc ξ ^ (-1 - 2 * ((0 : ℕ) : ℤ)) = (Jc ξ)⁻¹ := by
          intro ξ _
          norm_num
        by_cases hj : j = 0
        · refine ⟨fun ξ => (1 : ℂ) * starRingEnd ℂ (DZ H ξ) + (-1 : ℂ) * DZbar H ξ,
            hPcongr 1 1 _ _ _ (by norm_num) (by norm_num) (hPlin 1 1 1 (-1) _ _ hPAc hPB), ?_⟩
          intro ξ hξ
          obtain ⟨h1, h2⟩ := hbase ξ hξ
          have hne := hJcne ξ hξ
          rw [hpwcons, if_pos hj, hpw0, he0, h1, h2, hexp0 ξ hξ]
          field_simp
        · refine ⟨fun ξ => Complex.I * starRingEnd ℂ (DZ H ξ) + Complex.I * DZbar H ξ,
            hPcongr 1 1 _ _ _ (by norm_num) (by norm_num)
              (hPlin 1 1 Complex.I Complex.I _ _ hPAc hPB), ?_⟩
          intro ξ hξ
          obtain ⟨h1, h2⟩ := hbase ξ hξ
          have hne := hJcne ξ hξ
          rw [hpwcons, if_neg hj, hpw0, he1, h1, h2, hexp0 ξ hξ]
          field_simp
          ring
    | succ M ih =>
        -- ## Step 2: the inductive step
        intro v hv
        obtain ⟨j, v', rfl⟩ : ∃ (j : Fin 2) (t : List (Fin 2)), v = j :: t := by
          cases v with
          | nil => simp at hv
          | cons j t => exact ⟨j, t, rfl⟩
        have hlen : v'.length = M + 1 := by simpa using hv
        obtain ⟨Pv, hPv, hPveq⟩ := ih v' hlen
        obtain ⟨Q1, Q2, hQ1cls, hQ2cls, h4a, h4b⟩ :
            ∃ Q1 Q2 : ℂ → ℂ,
              PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1) Q1 ∧
              PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1) Q2 ∧
              (∀ ξ ∈ Ω, DZ (PartialWord v' chi) (H ξ)
                  = Jc ξ ^ (-3 - 2 * (M : ℤ)) * Q1 ξ) ∧
              (∀ ξ ∈ Ω, DZbar (PartialWord v' chi) (H ξ)
                  = Jc ξ ^ (-3 - 2 * (M : ℤ)) * Q2 ξ) := by
          -- ### Step 2d: the two class witnesses, built outside the per-point quantifier
          obtain ⟨QP1, hQP1cls, hQP1eq⟩ :=
            (PClassDerivClosed H Ω hΩ hH (4 * M + 1) (3 * M + 1) Pv hPv).1
          obtain ⟨QP2, hQP2cls, hQP2eq⟩ :=
            (PClassDerivClosed H Ω hΩ hH (4 * M + 1) (3 * M + 1) Pv hPv).2
          have hT1 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => R ζ * Pv ζ * starRingEnd ℂ (DZ H ζ)) :=
            hPcongr (3 + (4 * M + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 3 2 (4 * M + 1) (3 * M + 1) 1 1 R Pv
                (fun ζ => starRingEnd ℂ (DZ H ζ)) hR32 hPv hPAc)
          have hT2 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => Jc ζ * QP1 ζ * starRingEnd ℂ (DZ H ζ)) :=
            hPcongr (2 + (4 * M + 1 + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 2 2 (4 * M + 1 + 1) (3 * M + 1) 1 1 Jc QP1
                (fun ζ => starRingEnd ℂ (DZ H ζ)) hJ22 hQP1cls hPAc)
          have hT3 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => starRingEnd ℂ (R ζ) * Pv ζ * starRingEnd ℂ (DZbar H ζ)) :=
            hPcongr (3 + (4 * M + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 3 2 (4 * M + 1) (3 * M + 1) 1 1 (fun ζ => starRingEnd ℂ (R ζ)) Pv
                (fun ζ => starRingEnd ℂ (DZbar H ζ)) hRc32 hPv hPBc)
          have hT4 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => Jc ζ * QP2 ζ * starRingEnd ℂ (DZbar H ζ)) :=
            hPcongr (2 + (4 * M + 1 + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 2 2 (4 * M + 1 + 1) (3 * M + 1) 1 1 Jc QP2
                (fun ζ => starRingEnd ℂ (DZbar H ζ)) hJ22 hQP2cls hPBc)
          have hT5 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => starRingEnd ℂ (R ζ) * Pv ζ * DZ H ζ) :=
            hPcongr (3 + (4 * M + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 3 2 (4 * M + 1) (3 * M + 1) 1 1 (fun ζ => starRingEnd ℂ (R ζ)) Pv
                (DZ H) hRc32 hPv hPA)
          have hT6 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => Jc ζ * QP2 ζ * DZ H ζ) :=
            hPcongr (2 + (4 * M + 1 + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 2 2 (4 * M + 1 + 1) (3 * M + 1) 1 1 Jc QP2 (DZ H) hJ22 hQP2cls hPA)
          have hT7 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => R ζ * Pv ζ * DZbar H ζ) :=
            hPcongr (3 + (4 * M + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 3 2 (4 * M + 1) (3 * M + 1) 1 1 R Pv (DZbar H) hR32 hPv hPB)
          have hT8 : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1)
              (fun ζ => Jc ζ * QP1 ζ * DZbar H ζ) :=
            hPcongr (2 + (4 * M + 1 + 1) + 1) (2 + (3 * M + 1) + 1) _ _ _ (by omega) (by omega)
              (hPmul3 2 2 (4 * M + 1 + 1) (3 * M + 1) 1 1 Jc QP1 (DZbar H) hJ22 hQP1cls hPB)
          have hQ1cls : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1) (fun ζ =>
              (((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (R ζ * Pv ζ * starRingEnd ℂ (DZ H ζ))
                + (1 : ℂ) * (Jc ζ * QP1 ζ * starRingEnd ℂ (DZ H ζ)))
              - (((-1 - 2 * (M : ℤ) : ℤ) : ℂ)
                    * (starRingEnd ℂ (R ζ) * Pv ζ * starRingEnd ℂ (DZbar H ζ))
                + (1 : ℂ) * (Jc ζ * QP2 ζ * starRingEnd ℂ (DZbar H ζ)))) :=
            hPsub _ _ _ _ (hPlin _ _ _ 1 _ _ hT1 hT2) (hPlin _ _ _ 1 _ _ hT3 hT4)
          have hQ2cls : PClass H (4 * (M + 1) + 1) (3 * (M + 1) + 1) (fun ζ =>
              (((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (starRingEnd ℂ (R ζ) * Pv ζ * DZ H ζ)
                + (1 : ℂ) * (Jc ζ * QP2 ζ * DZ H ζ))
              - (((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (R ζ * Pv ζ * DZbar H ζ)
                + (1 : ℂ) * (Jc ζ * QP1 ζ * DZbar H ζ))) :=
            hPsub _ _ _ _ (hPlin _ _ _ 1 _ _ hT5 hT6) (hPlin _ _ _ 1 _ _ hT7 hT8)
          -- ### Steps 2a-2c: the chain-rule system, solved at each point of `Ω`
          have hboth : ∀ ξ ∈ Ω,
              DZ (PartialWord v' chi) (H ξ) = Jc ξ ^ (-3 - 2 * (M : ℤ)) *
                ((((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (R ξ * Pv ξ * starRingEnd ℂ (DZ H ξ))
                    + (1 : ℂ) * (Jc ξ * QP1 ξ * starRingEnd ℂ (DZ H ξ)))
                  - (((-1 - 2 * (M : ℤ) : ℤ) : ℂ)
                        * (starRingEnd ℂ (R ξ) * Pv ξ * starRingEnd ℂ (DZbar H ξ))
                    + (1 : ℂ) * (Jc ξ * QP2 ξ * starRingEnd ℂ (DZbar H ξ)))) ∧
              DZbar (PartialWord v' chi) (H ξ) = Jc ξ ^ (-3 - 2 * (M : ℤ)) *
                ((((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (starRingEnd ℂ (R ξ) * Pv ξ * DZ H ξ)
                    + (1 : ℂ) * (Jc ξ * QP2 ξ * DZ H ξ))
                  - (((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * (R ξ * Pv ξ * DZbar H ξ)
                    + (1 : ℂ) * (Jc ξ * QP1 ξ * DZbar H ξ))) := by
            intro ξ hξ
            have hne := hJcne ξ hξ
            have hpow1 : Jc ξ ^ (-1 - 2 * (M : ℤ))
                = Jc ξ ^ (-3 - 2 * (M : ℤ)) * Jc ξ * Jc ξ := by
              rw [← zpow_add_one₀ hne, ← zpow_add_one₀ hne]
              congr 1
              ring
            have hpow2 : Jc ξ ^ (-1 - 2 * (M : ℤ) - 1)
                = Jc ξ ^ (-3 - 2 * (M : ℤ)) * Jc ξ := by
              rw [← zpow_add_one₀ hne]
              congr 1
              ring
            obtain ⟨JP, hJP⟩ : ∃ f : ℂ → ℂ, f = fun z => Jc z ^ (-1 - 2 * (M : ℤ)) := ⟨_, rfl⟩
            have hJPval : JP ξ = Jc ξ ^ (-1 - 2 * (M : ℤ)) := by rw [hJP]
            have hJPd : DifferentiableAt ℝ JP ξ := by
              rw [hJP]
              have hout : HasDerivAt (fun y : ℂ => y ^ (-1 - 2 * (M : ℤ)))
                  (((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * Jc ξ ^ (-1 - 2 * (M : ℤ) - 1)) (Jc ξ) :=
                hasDerivAt_zpow _ (Jc ξ) (Or.inl hne)
              exact (hout.comp_hasFDerivAt ξ (hJcd ξ hξ).hasFDerivAt).differentiableAt
            have hPvd : DifferentiableAt ℝ Pv ξ :=
              ((PClassSmooth H Ω hΩ hH (4 * M + 1) (3 * M + 1) Pv hPv).differentiableOn
                (by simp)).differentiableAt (hΩ.mem_nhds hξ)
            have hDZJP : DZ JP ξ
                = ((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * Jc ξ ^ (-1 - 2 * (M : ℤ) - 1) * R ξ := by
              rw [hJP, (WirtingerPowerRule Jc Ω hΩ hJsm hJcne (-1 - 2 * (M : ℤ)) ξ hξ).1,
                hDZJc ξ hξ]
            have hDZbarJP : DZbar JP ξ
                = ((-1 - 2 * (M : ℤ) : ℤ) : ℂ) * Jc ξ ^ (-1 - 2 * (M : ℤ) - 1)
                    * starRingEnd ℂ (R ξ) := by
              rw [hJP, (WirtingerPowerRule Jc Ω hΩ hJsm hJcne (-1 - 2 * (M : ℤ)) ξ hξ).2,
                hDZbarJc ξ hξ]
            have hG2eq : (fun z => JP z * Pv z)
                = fun z => Jc z ^ (-1 - 2 * (M : ℤ)) * Pv z := by
              simp only [hJP]
            have hGee : (fun z => PartialWord v' chi (H z))
                =ᶠ[nhds ξ] (fun z => Jc z ^ (-1 - 2 * (M : ℤ)) * Pv z) :=
              Filter.eventuallyEq_of_mem (hΩ.mem_nhds hξ) (fun ζ hζ => hPveq ζ hζ)
            have hfdeq : fderiv ℝ (fun z => PartialWord v' chi (H z)) ξ
                = fderiv ℝ (fun z => Jc z ^ (-1 - 2 * (M : ℤ)) * Pv z) ξ := hGee.fderiv_eq
            have hDZeq : DZ (fun z => PartialWord v' chi (H z)) ξ
                = DZ (fun z => JP z * Pv z) ξ := by
              rw [DZ, DZ, hfdeq, hG2eq]
            have hDZbareq : DZbar (fun z => PartialWord v' chi (H z)) ξ
                = DZbar (fun z => JP z * Pv z) ξ := by
              rw [DZbar, DZbar, hfdeq, hG2eq]
            have hL1 : DZ (fun z => PartialWord v' chi (H z)) ξ
                = DZ JP ξ * Pv ξ + JP ξ * DZ Pv ξ := by
              rw [hDZeq, (WirtingerProductRule JP Pv ξ hJPd hPvd).1]
            have hL2 : DZbar (fun z => PartialWord v' chi (H z)) ξ
                = DZbar JP ξ * Pv ξ + JP ξ * DZbar Pv ξ := by
              rw [hDZbareq, (WirtingerProductRule JP Pv ξ hJPd hPvd).2]
            obtain ⟨hch1, hch2⟩ := WirtingerChainRule (PartialWord v' chi) H ξ
              (hHd ξ hξ) (hFd v' (H ξ) (hmaps ξ hξ))
            have eq1 : DZ (PartialWord v' chi) (H ξ) * DZ H ξ
                + DZbar (PartialWord v' chi) (H ξ) * starRingEnd ℂ (DZbar H ξ)
                = DZ JP ξ * Pv ξ + JP ξ * DZ Pv ξ := by rw [← hch1, hL1]
            have eq2 : DZ (PartialWord v' chi) (H ξ) * DZbar H ξ
                + DZbar (PartialWord v' chi) (H ξ) * starRingEnd ℂ (DZ H ξ)
                = DZbar JP ξ * Pv ξ + JP ξ * DZbar Pv ξ := by rw [← hch2, hL2]
            rw [hDZJP, hJPval, hQP1eq ξ hξ, hpow1, hpow2] at eq1
            rw [hDZbarJP, hJPval, hQP2eq ξ hξ, hpow1, hpow2] at eq2
            refine ⟨mul_right_cancel₀ hne ?_, mul_right_cancel₀ hne ?_⟩
            · linear_combination (starRingEnd ℂ (DZ H ξ)) * eq1
                - (starRingEnd ℂ (DZbar H ξ)) * eq2
                + (DZ (PartialWord v' chi) (H ξ)) * hdet ξ
            · linear_combination (DZ H ξ) * eq2 - (DZbar H ξ) * eq1
                + (DZbar (PartialWord v' chi) (H ξ)) * hdet ξ
          exact ⟨_, _, hQ1cls, hQ2cls, fun ξ hξ => (hboth ξ hξ).1, fun ξ hξ => (hboth ξ hξ).2⟩
        have hexp : ∀ x : ℂ, x ^ (-1 - 2 * (((M + 1 : ℕ)) : ℤ)) = x ^ (-3 - 2 * (M : ℤ)) := by
          intro x
          congr 1
          push_cast
          ring
        by_cases hj : j = 0
        · refine ⟨fun ξ => (1 : ℂ) * Q1 ξ + (1 : ℂ) * Q2 ξ,
            hPlin _ _ 1 1 _ _ hQ1cls hQ2cls, ?_⟩
          intro ξ hξ
          rw [hpwcons, if_pos hj, he0, h4a ξ hξ, h4b ξ hξ, hexp]
          ring
        · refine ⟨fun ξ => Complex.I * Q1 ξ + (-Complex.I) * Q2 ξ,
            hPlin _ _ Complex.I (-Complex.I) _ _ hQ1cls hQ2cls, ?_⟩
          intro ξ hξ
          rw [hpwcons, if_neg hj, he1, h4a ξ hξ, h4b ξ hξ, hexp]
          ring
  -- ## Step 3: conclusion
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = M + 1 := ⟨m - 1, by omega⟩
  obtain ⟨P, hP, hPeq⟩ := main M w (by omega)
  refine ⟨P, hPcongr _ _ _ _ _ (by omega) (by omega) hP, ?_⟩
  intro ξ hξ
  rw [hPeq ξ hξ, hJcpt]
  congr 2
  push_cast
  ring
