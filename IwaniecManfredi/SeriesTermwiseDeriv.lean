import IwaniecManfredi.Thm2TermSolvesEq18
import IwaniecManfredi.FourierCoefOde
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.FourierCoefForm36
import IwaniecManfredi.LambdaLinearLowerBound
import IwaniecManfredi.GammaRatioMinAtOne
import IwaniecManfredi.PartialWord
import IwaniecManfredi.Thm2TermWordDerivBound
import IwaniecManfredi.Thm2TermGeometricSummability
set_option maxHeartbeats 300000

/-- Term-by-term differentiation of the series (19), together with the
smoothness of `H` off the origin that it produces, which is the paper's
"we note that `lim λ_k = ∞`.  Therefore, we can perform any finite number of
term-by-term differentiations in formula (19)" (`paper.tex:387`), and the
estimate (43) read off from it.  The engine is `LambdaLinearLowerBound`'s
`λ_k ≥ (γ_n/(n+1))k` alone: it converts `ρ^{λ_k}` into a geometric `q^k` with
`q = ρ^{γ_n/(n+1)} < 1`, so the Cauchy-Schwarz tail
`Σ k^{2m-1} ρ^{2λ_k - 2λ_{n+1}}` of `paper.tex:391` converges for every `m`.
The constant lower bound `λ_k ≥ (p-1)/(np)` of (25) contributes nothing here:
it is constant in `k`, so it yields neither `λ_k → ∞` nor any decay. -/
theorem SeriesTermwiseDeriv (n : ℕ) (p : ℝ) (hn : 1 ≤ n) (hp : 1 < p)
    (H : ℂ → ℂ) (A : ℤ → ℂ)
    (hc : ContinuousOn H {ξ : ℂ | ‖ξ‖ < 1})
    (hw : MemWLocOn 1 2 {ξ : ℂ | ‖ξ‖ < 1} H)
    (hdiff : ∀ᵐ ξ : ℂ, ‖ξ‖ < 1 → DifferentiableAt ℝ H ξ)
    (h18 : SolvesEq18 n p {ξ : ℂ | ‖ξ‖ < 1} H)
    (hA : ∀ k : ℤ, (n : ℤ) ≤ |k| → ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      FourierCoefOfH n H k r = A k * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ))
    (hcomp : ∀ k : ℤ, (n : ℤ) ≤ k →
      A (-k) = ((EpsCoef n k.natAbs p : ℝ) : ℂ) * starRingEnd ℂ (A k))
    (hsum : Summable (fun m : ℕ => ((n : ℝ) + (m : ℝ)) * ‖A ((n : ℤ) + (m : ℤ))‖ ^ 2)) :
    (∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ < 1 →
      HasSum (fun m : ℕ => Thm2Term n p A (n + m) ξ) (H ξ)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ j : ℕ, n ≤ j → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ ρ →
        ‖H ξ - ∑ k ∈ Finset.Icc n j, Thm2Term n p A k ξ‖
          ≤ C * ‖ξ‖ ^ LambdaCoef n (j + 1) p) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ j : ℕ, n ≤ j → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ ρ →
        ‖HRad H ξ - ∑ k ∈ Finset.Icc n j, HRad (Thm2Term n p A k) ξ‖
          ≤ C * ‖ξ‖ ^ (LambdaCoef n (j + 1) p - 1)) ∧
    (A (n : ℤ) = 0 → ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ρ < 1 → ∃ Cm : ℝ, 0 ≤ Cm ∧
      ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ ≤ ρ →
        ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
          ≤ Cm * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) H ({ξ : ℂ | ‖ξ‖ < 1} \ {0}) := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hlamn, hepsn, hepsbd, hlambd⟩ := LambdaEpsEstimates n p hn hp
  -- `λ_{n+m} ≥ 0`, needed wherever a power of `λ` must be kept nonnegative
  have hL0 : ∀ m : ℕ, 0 ≤ LambdaCoef n (n + m) p := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.add_zero, hlamn]
    · have h1 := (hlambd (n + m) (by omega)).1
      have hnp : (0 : ℝ) < (n : ℝ) * p := by nlinarith
      have hq : (0 : ℝ) < (p - 1) / ((n : ℝ) * p) := div_pos (by linarith) hnp
      linarith
  -- (3): `λ_k` is nondecreasing in `k`, because the radicand of (20) is
  have hLmono : ∀ k k' : ℕ, k ≤ k' → LambdaCoef n k p ≤ LambdaCoef n k' p := by
    as_aux_lemma =>
      intro k k' hk
      have h1 : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk
      have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hsq : (k : ℝ) ^ 2 ≤ (k' : ℝ) ^ 2 := by nlinarith
      have hrad : 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2
          ≤ 4 * (k' : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
        linarith [mul_le_mul_of_nonneg_right hsq hp0.le]
      have hs := Real.sqrt_le_sqrt hrad
      simp only [LambdaCoef]
      linarith
  -- the reindexing `Icc n (n + J) ↔ range (J + 1)` of a finite head of (19)
  have hreindexC : ∀ (f : ℕ → ℂ) (J : ℕ),
      (∑ k ∈ Finset.Icc n (n + J), f k) = ∑ m ∈ Finset.range (J + 1), f (n + m) := by
    as_aux_lemma =>
      intro f J
      induction J with
      | zero => simp
      | succ J ih =>
          rw [show n + (J + 1) = (n + J) + 1 from by omega,
            Finset.sum_Icc_succ_top (by omega : n ≤ (n + J) + 1), ih,
            Finset.sum_range_succ (f := fun m => f (n + m)) (n := J + 1),
            show (n + J) + 1 = n + (J + 1) from by omega]
  -- the factorisation `x^c ≤ (ρ^{-a} x^a) ρ^c` for `0 < x ≤ ρ` and `a ≤ c`
  have hexpfac : ∀ ρ : ℝ, 0 < ρ → ∀ x : ℝ, 0 < x → x ≤ ρ → ∀ a c : ℝ, a ≤ c →
      x ^ c ≤ (ρ ^ (-a) * x ^ a) * ρ ^ c := by
    as_aux_lemma =>
      intro ρ hρ x hx hxρ a c hac
      have h1 : x ^ c = x ^ a * x ^ (c - a) := by
        rw [← Real.rpow_add hx]; ring_nf
      have h2 : x ^ (c - a) ≤ ρ ^ (c - a) := Real.rpow_le_rpow hx.le hxρ (by linarith)
      have h3 : ρ ^ (c - a) = ρ ^ (-a) * ρ ^ c := by
        rw [← Real.rpow_add hρ]; ring_nf
      have h4 : (0 : ℝ) ≤ x ^ a := Real.rpow_nonneg hx.le _
      calc x ^ c = x ^ a * x ^ (c - a) := h1
        _ ≤ x ^ a * ρ ^ (c - a) := mul_le_mul_of_nonneg_left h2 h4
        _ = (ρ ^ (-a) * x ^ a) * ρ ^ c := by rw [h3]; ring
  -- ## Steps 1 and 2: the summability engine.  `b` is an opaque positive linear rate
  -- for `λ`, `CA` an opaque bound on `|A_k|`, and together they turn every tail of
  -- the series into a geometric one at every polynomial weight.
  obtain ⟨b, CA, hb0, hbhalf, hbL, hCA0, hCA, hqbd, hgeo, hTn, hT2, hgeo0⟩ :=
    Thm2TermGeometricSummability n p hn hp A hsum
  have hnormsum : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      Summable (fun m : ℕ => ‖Thm2Term n p A (n + m) ξ‖) := by
    intro ξ hξ hξ1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hT2 m ξ hξ)
      (hgeo0 ‖ξ‖ hr hξ1)
  -- ## Steps 3 and 4: estimate (11), the all-order word-derivative bound on a single
  -- summand, together with the smoothness of that summand off the origin.  Both are
  -- `Thm2TermWordDerivBound`: its `E`-class calculus needs no sector decomposition,
  -- since `T_k` is a two-term combination of the monomials `E s j l ξ = |ξ|^s ξ^j
  -- conj(ξ)^l`, the class is closed under `∂/∂ξ` and `∂/∂conj(ξ)`, and one
  -- differentiation multiplies the frequency bound by `2(K + |w|)` and lowers the
  -- common exponent by one.
  obtain ⟨Dw, Vp, hDwnil, hDwcons, hVpv, Vpcons, Vpnonneg, Trepbd, hTcd⟩ :=
    Thm2TermWordDerivBound n p hn hp A
  -- the bridge from the paper's `D^ν` to `Dw`: `PartialWord` differentiates along the
  -- unit directions `1` and `i`, so the `Vp` factor of its word is `1`
  have PWrep : ∀ (w : List (Fin 2)) (f : ℂ → ℂ),
      PartialWord w f
        = Dw (w.map (fun j : Fin 2 => if j = 0 then (1 : ℂ) else Complex.I)) f := by
    intro w f
    induction w with
    | nil => rw [List.map_nil, hDwnil]; rfl
    | cons j w ih =>
        have h1 : PartialWord (j :: w) f
            = fun z : ℂ =>
              fderiv ℝ (PartialWord w f) z (if j = 0 then (1 : ℂ) else Complex.I) := rfl
        rw [h1, ih, List.map_cons, hDwcons]
  have PWlen : ∀ w : List (Fin 2),
      (w.map (fun j : Fin 2 => if j = 0 then (1 : ℂ) else Complex.I)).length = w.length :=
    fun w => List.length_map _
  have PWVp : ∀ w : List (Fin 2),
      Vp (w.map (fun j : Fin 2 => if j = 0 then (1 : ℂ) else Complex.I)) = 1 := by
    intro w
    induction w with
    | nil => rw [List.map_nil, hVpv]; simp
    | cons j w ih =>
        rw [List.map_cons, Vpcons, ih, mul_one]
        rcases eq_or_ne j 0 with h | h
        · rw [if_pos h]; simp
        · rw [if_neg h]; simp
  -- estimate (11)
  have Televen : ∀ (w : List (Fin 2)) (m : ℕ) (ξ : ℂ), ξ ≠ 0 →
      ‖PartialWord w (Thm2Term n p A (n + m)) ξ‖
        ≤ (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1))
              + (w.length : ℝ))) ^ (w.length)
            * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
          * ‖ξ‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) := by
    intro w m ξ hξ
    have h :=
      Trepbd (w.map (fun j : Fin 2 => if j = 0 then (1 : ℂ) else Complex.I)) m ξ hξ
    rw [PWVp, PWlen] at h
    rw [PWrep]
    simpa using h
  -- ## Step 5 preparation: the Fourier side.  `FourierCoefRegularity` and
  -- `FourierCoefOde` apply under (H1), (H2), and `FourierCoefForm36` then kills the
  -- coefficients of index `|j| < n`.
  obtain ⟨hacont, -, -, -, -, hfreg⟩ := FourierCoefRegularity n H hc hw hdiff
  obtain ⟨hode1, hode2, hsmo⟩ := FourierCoefOde n p hn hp H hc hw hdiff h18
  have hlow : ∀ (j : ℤ) (r : ℝ), j.natAbs < n → r ∈ Set.Ico (0 : ℝ) 1 →
      FourierCoefOfH n H j r = 0 := fun j r hj hr =>
    (FourierCoefForm36 n p j hn hp (FourierCoefOfH n H j) (hacont j) (hsmo j)
      (fun s hs => hode2 j s hs)).1 hj r hr
  -- (4): the polar form of a single summand
  have h40 : ∀ k : ℕ, n ≤ k → ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ((r ^ LambdaCoef n k p : ℝ) : ℂ)
            * (A (k : ℤ) * Complex.exp ((((k : ℤ) - (n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
              + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                  * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ)
                      * (θ : ℂ) * Complex.I)) :=
    fun k hk r hr θ => (Thm2TermSolvesEq18 n p hn hp k hk A).2.1 r hr θ
  -- the fold `j ↔ -j`: the `j = k` and `j = -k` terms of the symmetric Fourier sum
  -- add up to `T_k`
  have hpair : ∀ (k : ℕ), n ≤ k → ∀ (r : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 → ∀ θ : ℝ,
      FourierCoefOfH n H (k : ℤ) r
            * Complex.exp (((((k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
          + FourierCoefOfH n H (-(k : ℤ)) r
            * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        = Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro k hk r hr θ
    have hkabs : (n : ℤ) ≤ |(k : ℤ)| := by
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ))]
      exact_mod_cast hk
    have hkabs' : (n : ℤ) ≤ |(-(k : ℤ))| := by
      rw [abs_neg]
      exact hkabs
    have hnat1 : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
    have hnat2 : ((-(k : ℤ))).natAbs = k := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    have hAneg : A (-(k : ℤ)) = ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ)) := by
      have h := hcomp (k : ℤ) (by exact_mod_cast hk)
      rw [hnat1] at h
      exact h
    rw [hA (k : ℤ) hkabs r hr, hA (-(k : ℤ)) hkabs' r hr, hnat1, hnat2, hAneg,
      h40 k hk r hr.1 θ]
    ring
  -- the symmetric partial sum of `H`'s Fourier series is the partial sum of (19)
  have hfold : ∀ (N : ℕ) (r : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 → ∀ θ : ℝ,
      (∑ j ∈ Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ),
          FourierCoefOfH n H j r
            * Complex.exp ((((j - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I))
        = ∑ k ∈ Finset.Icc n (n + N),
            Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro N r hr θ
    induction N with
    | zero =>
        have hmid : ∀ j ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ),
            FourierCoefOfH n H j r
              * Complex.exp ((((j - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I) = 0 := by
          intro j hj
          simp only [Finset.mem_Ioo] at hj
          rw [hlow j r (by omega) ⟨le_of_lt hr.1, hr.2⟩, zero_mul]
        have hsplit : Finset.Icc (-((n + 0 : ℕ) : ℤ)) ((n + 0 : ℕ) : ℤ)
            = insert (-(n : ℤ)) (insert (n : ℤ) (Finset.Ioo (-(n : ℤ)) (n : ℤ))) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
          omega
        have hni : (n : ℤ) ∉ Finset.Ioo (-(n : ℤ)) (n : ℤ) := by simp
        have hnni : (-(n : ℤ)) ∉ insert (n : ℤ) (Finset.Ioo (-(n : ℤ)) (n : ℤ)) := by
          simp only [Finset.mem_insert, Finset.mem_Ioo]
          have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
          omega
        rw [hsplit, Finset.sum_insert hnni, Finset.sum_insert hni,
          Finset.sum_eq_zero hmid, add_zero,
          show Finset.Icc n (n + 0) = {n} from by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_singleton]
            omega,
          Finset.sum_singleton]
        have h := hpair n le_rfl r hr θ
        push_cast at h ⊢
        linear_combination h
    | succ N ih =>
        have hsplit : Finset.Icc (-((n + (N + 1) : ℕ) : ℤ)) ((n + (N + 1) : ℕ) : ℤ)
            = insert (-((n + (N + 1) : ℕ) : ℤ))
                (insert (((n + (N + 1) : ℕ) : ℤ))
                  (Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ))) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          push_cast
          omega
        have hni : (((n + (N + 1) : ℕ) : ℤ))
            ∉ Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ) := by
          simp only [Finset.mem_Icc]
          push_cast
          omega
        have hnni : (-((n + (N + 1) : ℕ) : ℤ))
            ∉ insert (((n + (N + 1) : ℕ) : ℤ))
                (Finset.Icc (-((n + N : ℕ) : ℤ)) ((n + N : ℕ) : ℤ)) := by
          simp only [Finset.mem_insert, Finset.mem_Icc]
          have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
          push_cast
          omega
        have hRsplit : Finset.Icc n (n + (N + 1))
            = insert (n + (N + 1)) (Finset.Icc n (n + N)) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hRni : (n + (N + 1)) ∉ Finset.Icc n (n + N) := by
          simp only [Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert hnni, Finset.sum_insert hni, ih,
          hRsplit, Finset.sum_insert hRni]
        have h := hpair (n + (N + 1)) (by omega) r hr θ
        push_cast at h ⊢
        linear_combination h
  -- ## Step 5: conjunct (a).  Part (f) of `FourierCoefRegularity` gives `L²`
  -- convergence of the SYMMETRIC Fourier partial sums; the fold turns those into the
  -- partial sums of (19), which converge UNIFORMLY by (5) and (6).  The two limits
  -- therefore agree in `L²`, and continuity upgrades that to a pointwise identity.
  have hcircle : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → ∀ θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
      H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = ∑' m : ℕ, Thm2Term n p A (n + m)
            ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro r hr
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hcnorm : ∀ θ : ℝ, ‖((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ = r := by
      intro θ
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1]
    have hcne : ∀ θ : ℝ, ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
      intro θ hcon
      have h := hcnorm θ
      rw [hcon, norm_zero] at h
      exact absurd h.symm (ne_of_gt hr.1)
    -- the majorant, introduced opaquely so the shift lemmas never see its body
    obtain ⟨u, hudef⟩ : ∃ u : ℕ → ℝ, ∀ m : ℕ,
        u m = 2 * ‖A ((n : ℤ) + (m : ℤ))‖ * r ^ LambdaCoef n (n + m) p := ⟨_, fun _ => rfl⟩
    have hu : Summable u := (hgeo0 r hr.1 hr.2).congr (fun m => (hudef m).symm)
    have hTb : ∀ (m : ℕ) (θ : ℝ),
        ‖Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ u m := by
      intro m θ
      rw [hudef m]
      have h := hT2 m _ (hcne θ)
      rwa [hcnorm θ] at h
    have hTcont : ∀ m : ℕ, Continuous (fun θ : ℝ =>
        Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      intro m
      have he : (fun θ : ℝ =>
            Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          = fun θ : ℝ => ((r ^ LambdaCoef n (n + m) p : ℝ) : ℂ)
              * (A (((n + m : ℕ)) : ℤ)
                    * Complex.exp (((((n + m : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℂ)
                        * (θ : ℂ) * Complex.I)
                + ((EpsCoef n (n + m) p : ℝ) : ℂ) * starRingEnd ℂ (A (((n + m : ℕ)) : ℤ))
                    * Complex.exp (((-(((n + m : ℕ)) : ℤ) - (n : ℤ) : ℤ) : ℂ)
                        * (θ : ℂ) * Complex.I)) := by
        funext θ
        exact h40 (n + m) (by omega) r hr.1 θ
      rw [he]
      fun_prop
    have hFcont : Continuous (fun θ : ℝ =>
        ∑' m : ℕ, Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
      continuous_tsum hTcont hu (fun m θ => hTb m θ)
    have hHcont : Continuous (fun θ : ℝ =>
        H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      refine hc.comp_continuous (by fun_prop) (fun θ => ?_)
      show ‖_‖ < 1
      rw [hcnorm θ]
      exact hr.2
    have hScont : ∀ N : ℕ, Continuous (fun θ : ℝ =>
        ∑ k ∈ Finset.Icc n (n + N),
          Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      intro N
      refine continuous_finsetSum _ (fun k hk => ?_)
      have he : (fun θ : ℝ => Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          = fun θ : ℝ => ((r ^ LambdaCoef n k p : ℝ) : ℂ)
              * (A (k : ℤ)
                    * Complex.exp (((((k : ℤ) - (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
                + ((EpsCoef n k p : ℝ) : ℂ) * starRingEnd ℂ (A (k : ℤ))
                    * Complex.exp ((((-(k : ℤ) - (n : ℤ)) : ℤ) : ℂ)
                        * (θ : ℂ) * Complex.I)) := by
        funext θ
        exact h40 k (Finset.mem_Icc.mp hk).1 r hr.1 θ
      rw [he]
      fun_prop
    -- the `L²` convergence of the symmetric partial sums, reindexed and folded
    have hI : Filter.Tendsto (fun N : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - ∑ k ∈ Finset.Icc n (n + N),
              Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        Filter.atTop (nhds 0) := by
      have hcomp' := (hfreg r ⟨le_of_lt hr.1, hr.2⟩).comp (Filter.tendsto_add_atTop_nat n)
      refine hcomp'.congr (fun N => ?_)
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      show ‖_ - ∑ j ∈ Finset.Icc (-((N + n : ℕ) : ℤ)) ((N + n : ℕ) : ℤ), _‖ ^ 2 = _
      rw [show (N + n : ℕ) = (n + N : ℕ) from by omega, hfold N r hr θ]
    -- the uniform tail bound on the partial sums of (19)
    have hreidx : ∀ (N : ℕ) (θ : ℝ),
        (∑ k ∈ Finset.Icc n (n + N),
            Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          = ∑ m ∈ Finset.range (N + 1),
              Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
      intro N θ
      induction N with
      | zero => simp
      | succ N ih =>
          rw [show n + (N + 1) = (n + N) + 1 from by omega,
            Finset.sum_Icc_succ_top (by omega : n ≤ (n + N) + 1), ih,
            Finset.sum_range_succ (f := fun m => Thm2Term n p A (n + m)
              ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (n := N + 1),
            show (n + N) + 1 = n + (N + 1) from by omega]
    have htailb : ∀ (N : ℕ) (θ : ℝ),
        ‖(∑' m : ℕ, Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            - ∑ k ∈ Finset.Icc n (n + N),
                Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
          ≤ ∑' m : ℕ, u (m + (N + 1)) := by
      intro N θ
      have hshift : Summable (fun m : ℕ => u (m + (N + 1))) :=
        (summable_nat_add_iff (N + 1)).mpr hu
      have hsn : Summable (fun m : ℕ => ‖Thm2Term n p A (n + (m + (N + 1)))
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
        Summable.of_nonneg_of_le (fun m => norm_nonneg _)
          (fun m => hTb (m + (N + 1)) θ) hshift
      have hs : Summable (fun m : ℕ =>
          Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
        Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
          (fun m => hTb m θ) hu)
      have hsplit := hs.sum_add_tsum_nat_add (N + 1)
      rw [hreidx N θ, ← hsplit]
      have he : (∑ i ∈ Finset.range (N + 1),
            Thm2Term n p A (n + i) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          + (∑' i : ℕ, Thm2Term n p A (n + (i + (N + 1)))
              ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
          - ∑ m ∈ Finset.range (N + 1),
              Thm2Term n p A (n + m) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          = ∑' i : ℕ, Thm2Term n p A (n + (i + (N + 1)))
              ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
        ring
      rw [he]
      refine le_trans (norm_tsum_le_tsum_norm hsn) ?_
      exact Summable.tsum_le_tsum (fun m => hTb (m + (N + 1)) θ) hsn hshift
    have htail0 : Filter.Tendsto (fun N : ℕ => ∑' m : ℕ, u (m + (N + 1)))
        Filter.atTop (nhds 0) :=
      (tendsto_sum_nat_add u).comp (Filter.tendsto_add_atTop_nat 1)
    -- the two limits agree in `L²`
    have hzero : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - ∑' m : ℕ, Thm2Term n p A (n + m)
              ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) = 0 := by
      have hb : ∀ N : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
            ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              - ∑' m : ℕ, Thm2Term n p A (n + m)
                  ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
          ≤ 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi),
              ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - ∑ k ∈ Finset.Icc n (n + N),
                    Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
            + 2 * (∑' m : ℕ, u (m + (N + 1))) ^ 2 * (2 * Real.pi) := by
        intro N
        have hI1 : IntervalIntegrable (fun θ : ℝ =>
            ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              - ∑' m : ℕ, Thm2Term n p A (n + m)
                  ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
            MeasureTheory.volume 0 (2 * Real.pi) :=
          ((hHcont.sub hFcont).norm.pow 2).intervalIntegrable _ _
        have hI2 : IntervalIntegrable (fun θ : ℝ =>
            2 * ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - ∑ k ∈ Finset.Icc n (n + N),
                    Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
              + 2 * (∑' m : ℕ, u (m + (N + 1))) ^ 2) MeasureTheory.volume 0 (2 * Real.pi) :=
          ((((hHcont.sub (hScont N)).norm.pow 2).const_mul 2).add
            continuous_const).intervalIntegrable _ _
        have hI3 : IntervalIntegrable (fun θ : ℝ =>
            2 * ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - ∑ k ∈ Finset.Icc n (n + N),
                    Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
            MeasureTheory.volume 0 (2 * Real.pi) :=
          (((hHcont.sub (hScont N)).norm.pow 2).const_mul 2).intervalIntegrable _ _
        have hmono := intervalIntegral.integral_mono_on h2pi hI1 hI2 (fun θ _ => ?_)
        · refine le_trans hmono (le_of_eq ?_)
          rw [intervalIntegral.integral_add hI3 (intervalIntegrable_const),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp only [smul_eq_mul, sub_zero]
          ring
        · have h1 : ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              - ∑' m : ℕ, Thm2Term n p A (n + m)
                  ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
            ≤ ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - ∑ k ∈ Finset.Icc n (n + N),
                    Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
              + ∑' m : ℕ, u (m + (N + 1)) := by
            have e1 := norm_sub_le_norm_sub_add_norm_sub
              (H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              (∑ k ∈ Finset.Icc n (n + N),
                Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              (∑' m : ℕ, Thm2Term n p A (n + m)
                ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
            have e2 := htailb N θ
            rw [← norm_neg (_ - _), neg_sub] at e2
            linarith
          have h2 : (0 : ℝ) ≤ ∑' m : ℕ, u (m + (N + 1)) :=
            tsum_nonneg (fun m => by
              rw [hudef]
              exact mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _))
          have h3 : (0 : ℝ) ≤ ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              - ∑ k ∈ Finset.Icc n (n + N),
                  Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ :=
            norm_nonneg _
          nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2,
            sq_nonneg (‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
              - ∑ k ∈ Finset.Icc n (n + N),
                  Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
              - ∑' m : ℕ, u (m + (N + 1)))]
      have hlim : Filter.Tendsto (fun N : ℕ =>
          2 * (∫ θ in (0 : ℝ)..(2 * Real.pi),
              ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
                - ∑ k ∈ Finset.Icc n (n + N),
                    Thm2Term n p A k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
            + 2 * (∑' m : ℕ, u (m + (N + 1))) ^ 2 * (2 * Real.pi))
          Filter.atTop (nhds 0) := by
        have h1 := hI.const_mul 2
        have h2 := ((htail0.pow 2).const_mul 2).mul_const (2 * Real.pi)
        have h3 := h1.add h2
        norm_num at h3
        exact h3
      have hle := ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
      have hge : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
            - ∑' m : ℕ, Thm2Term n p A (n + m)
                ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 :=
        intervalIntegral.integral_nonneg h2pi (fun θ _ => by positivity)
      linarith
    -- and the identity is pointwise, both sides being continuous
    intro θ hθ
    have hae : (fun θ : ℝ => ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          - ∑' m : ℕ, Thm2Term n p A (n + m)
              ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
      refine (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae ?_
        ((hHcont.sub hFcont).norm.pow 2).integrableOn_Ioc).mp ?_
      · filter_upwards with θ
        exact pow_two_nonneg _
      · rw [← intervalIntegral.integral_of_le h2pi]
        exact hzero
    have heq := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := MeasureTheory.volume) hae
      (((hHcont.sub hFcont).norm.pow 2).continuousOn) continuousOn_const
    have h0 := heq hθ
    simp only [Pi.zero_apply] at h0
    have h1 : H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        - ∑' m : ℕ, Thm2Term n p A (n + m)
            ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0)
    linear_combination h1
  -- ## conjunct (a): the circle identity at radius `‖ξ‖`, after normalising `arg ξ`
  -- from `(-π, π]` into `(0, 2π]`.
  have hasum : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ < 1 →
      HasSum (fun m : ℕ => Thm2Term n p A (n + m) ξ) (H ξ) := by
    intro ξ hξ hξ1
    have hξne : ξ ≠ 0 := norm_pos_iff.mp hξ
    have harg := Complex.arg_mem_Ioc ξ
    have hper : ∀ θ : ℝ, Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((θ : ℂ) * Complex.I) := by
      intro θ
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have hfinish : ∀ θ : ℝ, θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) →
        ξ = ((‖ξ‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) →
        HasSum (fun m : ℕ => Thm2Term n p A (n + m) ξ) (H ξ) := by
      intro θ hθ hξθ
      have heq := hcircle ‖ξ‖ ⟨hξ, hξ1⟩ θ hθ
      rw [← hξθ] at heq
      rw [heq]
      exact (Summable.of_norm (hnormsum ξ hξne hξ1)).hasSum
    rcases le_or_gt (Complex.arg ξ) 0 with hnpos | hpos
    · refine hfinish (Complex.arg ξ + 2 * Real.pi) ⟨by linarith [harg.1], by linarith⟩ ?_
      rw [hper (Complex.arg ξ)]
      exact (Complex.norm_mul_exp_arg_mul_I ξ).symm
    · refine hfinish (Complex.arg ξ) ⟨hpos, by linarith [harg.2]⟩ ?_
      exact (Complex.norm_mul_exp_arg_mul_I ξ).symm
  -- ## Step 6: estimate (13), `D^w H(ξ) = Σ_{k ≥ n} D^w T_k(ξ)` for EVERY word.  This is
  -- the only route to the derivatives of `H` appearing in (c) and (d), since no
  -- smoothness of `H` is assumed; (13′), delivered by the same induction, is conjunct (e).
  have hHval : ∀ ξ : ℂ, ξ ≠ 0 → ‖ξ‖ < 1 →
      H ξ = ∑' m : ℕ, Thm2Term n p A (n + m) ξ := fun ξ hξ hξ1 =>
    ((hasum ξ (norm_pos_iff.mpr hξ) hξ1).tsum_eq).symm
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the Wirtinger-free reconstruction of a real-linear map on `ℂ` from its two values
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ), ∀ (q : ℂ × ℂ) (v : ℂ),
      Θ q v = (v.re : ℂ) * q.1 + (v.im : ℂ) * q.2 := by
    refine ⟨(ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)
      + (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).comp
        (ContinuousLinearMap.snd ℝ ℂ ℂ), ?_⟩
    intro q v
    simp [ContinuousLinearMap.smulRightL_apply_apply, Complex.real_smul]
  have hdecompCLM : ∀ (L : ℂ →L[ℝ] ℂ) (v : ℂ),
      L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
    as_aux_lemma =>
      intro L v
      calc L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := by
            congr 1
            rw [Complex.real_smul, Complex.real_smul, mul_one]
            exact (Complex.re_add_im v).symm
        _ = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
            rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  -- agreement of two functions on an OPEN set propagates to every word derivative
  have DwcongrOn : ∀ (w : List ℂ) (f g : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      (∀ z ∈ U, f z = g z) → ∀ z ∈ U, Dw w f z = Dw w g z := by
    as_aux_lemma =>
      intro w
      induction w with
      | nil => intro f g U hU h z hz; rw [hDwnil, hDwnil]; exact h z hz
      | cons v w ih =>
          intro f g U hU h z hz
          rw [hDwcons, hDwcons]
          show fderiv ℝ (Dw w f) z v = fderiv ℝ (Dw w g) z v
          have he : fderiv ℝ (Dw w f) z = fderiv ℝ (Dw w g) z :=
            Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hz)
              (fun y hy => ih f g U hU h y hy))
          rw [he]
  -- the annulus reduction: a ball of radius `min (‖x‖/2) ((1-‖x‖)/2)` about a point of
  -- the punctured disc stays in the annulus `‖x‖/2 ≤ ‖z‖ < (1+‖x‖)/2`
  have hsub : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      z ≠ 0 ∧ ‖z‖ < (1 + ‖x‖) / 2 ∧ ‖x‖ / 2 ≤ ‖z‖ := by
    as_aux_lemma =>
      intro x hx0 hx1 z hz
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hdz : ‖z - x‖ < min (‖x‖ / 2) ((1 - ‖x‖) / 2) := by
        rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hd1 : ‖z - x‖ < ‖x‖ / 2 := lt_of_lt_of_le hdz (min_le_left _ _)
      have hd2 : ‖z - x‖ < (1 - ‖x‖) / 2 := lt_of_lt_of_le hdz (min_le_right _ _)
      have hA1 := norm_sub_norm_le z x
      have hA2 := norm_sub_norm_le x z
      rw [norm_sub_rev] at hA2
      have hzlow : ‖x‖ / 2 ≤ ‖z‖ := by linarith
      refine ⟨?_, by linarith, hzlow⟩
      intro hz0
      rw [hz0, norm_zero] at hzlow
      linarith
  -- the majorant of (11) on such a ball, introduced opaquely and parameterized by the centre
  obtain ⟨uu, huu⟩ : ∃ uu : ℂ → ℕ → ℝ → ℕ → ℝ, ∀ (x : ℂ) (M : ℕ) (P : ℝ) (m : ℕ),
      uu x M P m = 2 * (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M * P
            * ((‖x‖ / 2) ^ (-(M : ℝ)))
          * (((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
              * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := ⟨_, fun _ _ _ _ => rfl⟩
  have huusum : ∀ (x : ℂ) (M : ℕ) (P : ℝ), x ≠ 0 → ‖x‖ < 1 → Summable (uu x M P) := by
    as_aux_lemma =>
      intro x M P hx0 hx1
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hρ2 : (0 : ℝ) < (1 + ‖x‖) / 2 := by linarith
      have hρ21 : (1 + ‖x‖) / 2 < 1 := by linarith
      have he : uu x M P = fun m : ℕ =>
          (2 * (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M * P * ((‖x‖ / 2) ^ (-(M : ℝ))))
            * (((n : ℝ) + (m : ℝ)) ^ M * ‖A ((n : ℤ) + (m : ℤ))‖
                * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := by
        funext m
        rw [huu]
      rw [he]
      exact (hgeo M ((1 + ‖x‖) / 2) hρ2 hρ21).mul_left _
  have huulin : ∀ (x : ℂ) (M : ℕ) (P c : ℝ) (m : ℕ),
      uu x M (c * P) m = uu x M P m * c := by
    as_aux_lemma =>
      intro x M P c m
      rw [huu, huu]
      ring
  have huunn : ∀ (x : ℂ) (M : ℕ) (P : ℝ), x ≠ 0 → 0 ≤ P → ∀ m : ℕ, 0 ≤ uu x M P m := by
    as_aux_lemma =>
      intro x M P hx0 hP m
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hρ1 : (0 : ℝ) < ‖x‖ / 2 := by positivity
      have hρ2 : (0 : ℝ) < (1 + ‖x‖) / 2 := by positivity
      rw [huu]
      have h1 : (0 : ℝ) ≤ (2 * (3 + Real.sqrt (p - 1) + (M : ℝ))) ^ M := by positivity
      have h2 : (0 : ℝ) ≤ ((‖x‖ / 2) ^ (-(M : ℝ))) := Real.rpow_nonneg hρ1.le _
      have h3 : (0 : ℝ) ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) :=
        Real.rpow_nonneg hρ2.le _
      have h4 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
      have h5 : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ)) ^ M := by positivity
      positivity
  -- the uniform bound on the ball: this is (11) with `‖ξ‖^{λ_k - m} ≤ δ^{-m} ρ^{λ_k}`
  have hub : ∀ (w : List ℂ) (m : ℕ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      ‖Dw w (Thm2Term n p A (n + m)) z‖ ≤ uu x w.length (Vp w) m := by
    as_aux_lemma =>
      intro w m x hx0 hx1 z hz
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hρ1 : (0 : ℝ) < ‖x‖ / 2 := by positivity
      have hρ2 : (0 : ℝ) < (1 + ‖x‖) / 2 := by linarith
      obtain ⟨hz0, hzup, hzlow⟩ := hsub x hx0 hx1 z hz
      have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      refine le_trans (Trepbd w m z hz0) ?_
      have hX1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hc1 : (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
          ≤ ((n : ℝ) + (m : ℝ)) * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) := by
        have h2 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
        have h1 : (w.length : ℝ) ≤ ((n : ℝ) + (m : ℝ)) * (w.length : ℝ) := by
          calc (w.length : ℝ) = 1 * (w.length : ℝ) := (one_mul _).symm
            _ ≤ ((n : ℝ) + (m : ℝ)) * (w.length : ℝ) := mul_le_mul_of_nonneg_right hX1 h2
        have h3 : ((n : ℝ) + (m : ℝ)) * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ)))
            = 2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)))
              + 2 * (((n : ℝ) + (m : ℝ)) * (w.length : ℝ)) := by ring
        rw [h3]
        linarith
      have hc1p : (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
            ^ (w.length)
          ≤ ((n : ℝ) + (m : ℝ)) ^ (w.length)
              * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hc1 _
      have hp2 : ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
          ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) * ((‖x‖ / 2) ^ (-(w.length : ℝ))) := by
        have hsplit : ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
            = ‖z‖ ^ (LambdaCoef n (n + m) p) * ‖z‖ ^ (-(w.length : ℝ)) := by
          rw [← Real.rpow_add hzr]
          ring_nf
        rw [hsplit]
        have hA : ‖z‖ ^ (LambdaCoef n (n + m) p)
            ≤ ((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p) :=
          Real.rpow_le_rpow (norm_nonneg _) hzup.le (hL0 m)
        have hB : ‖z‖ ^ (-(w.length : ℝ)) ≤ (‖x‖ / 2) ^ (-(w.length : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hρ1 hzlow (by
            have : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
            linarith)
        exact mul_le_mul hA hB (Real.rpow_nonneg hzr.le _) (Real.rpow_nonneg hρ2.le _)
      rw [huu]
      have hVp : (0 : ℝ) ≤ Vp w := Vpnonneg w
      have hA0 : (0 : ℝ) ≤ ‖A ((n : ℤ) + (m : ℤ))‖ := norm_nonneg _
      have hfac : (0 : ℝ) ≤ Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖) := by positivity
      have hpz : (0 : ℝ) ≤ ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hbig : (0 : ℝ) ≤ (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) := by
        positivity
      have hrp1 : (0 : ℝ) ≤ ((‖x‖ / 2) ^ (-(w.length : ℝ))) := Real.rpow_nonneg hρ1.le _
      have hrp2 : (0 : ℝ) ≤ (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p)) :=
        Real.rpow_nonneg hρ2.le _
      have hXn : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ)) ^ (w.length) := by positivity
      calc (2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ))) ^ (w.length)
              * Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖)
            * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))
          = ((2 * (((n : ℝ) + (m : ℝ)) * (3 + Real.sqrt (p - 1)) + (w.length : ℝ)))
                ^ (w.length))
              * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
                * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))) := by ring
        _ ≤ (((n : ℝ) + (m : ℝ)) ^ (w.length)
                * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length))
              * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
                * ‖z‖ ^ (LambdaCoef n (n + m) p - (w.length : ℝ))) := by
            refine mul_le_mul_of_nonneg_right hc1p ?_
            exact mul_nonneg hfac hpz
        _ ≤ (((n : ℝ) + (m : ℝ)) ^ (w.length)
                * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length))
              * ((Vp w * (2 * ‖A ((n : ℤ) + (m : ℤ))‖))
                * ((((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))
                    * ((‖x‖ / 2) ^ (-(w.length : ℝ))))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp2 hfac) ?_
            positivity
        _ = 2 * (2 * (3 + Real.sqrt (p - 1) + (w.length : ℝ))) ^ (w.length) * Vp w
                * ((‖x‖ / 2) ^ (-(w.length : ℝ)))
              * (((n : ℝ) + (m : ℝ)) ^ (w.length) * ‖A ((n : ℤ) + (m : ℤ))‖
                  * (((1 + ‖x‖) / 2) ^ (LambdaCoef n (n + m) p))) := by ring
  have hssum : ∀ (w : List ℂ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      Summable (fun m : ℕ => Dw w (Thm2Term n p A (n + m)) z) := by
    as_aux_lemma =>
    intro w x hx0 hx1 z hz
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hub w m x hx0 hx1 z hz) (huusum x w.length (Vp w) hx0 hx1))
  have hfdbd : ∀ (w : List ℂ) (m : ℕ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      ‖fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z‖ ≤ uu x (w.length + 1) (Vp w) m := by
    as_aux_lemma =>
      intro w m x hx0 hx1 z hz
      refine ContinuousLinearMap.opNorm_le_bound _
        (huunn x _ _ hx0 (Vpnonneg w) m) (fun v => ?_)
      have he : fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z v
          = Dw (v :: w) (Thm2Term n p A (n + m)) z := by
        rw [hDwcons]
      rw [he]
      have h1 := hub (v :: w) m x hx0 hx1 z hz
      have h2 : uu x (v :: w).length (Vp (v :: w)) m = uu x (w.length + 1) (Vp w) m * ‖v‖ := by
        rw [Vpcons, show (v :: w).length = w.length + 1 from by simp, huulin]
      rw [h2] at h1
      exact h1
  have hfdsum : ∀ (w : List ℂ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      Summable (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z) := by
    as_aux_lemma =>
    intro w x hx0 hx1 z hz
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hfdbd w m x hx0 hx1 z hz) (huusum x (w.length + 1) (Vp w) hx0 hx1))
  have hfd : ∀ (w : List ℂ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      HasFDerivAt (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y)
        (∑' m : ℕ, fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z) z := by
    as_aux_lemma =>
    intro w x hx0 hx1 z hz
    have hrad0 : (0 : ℝ) < min (‖x‖ / 2) ((1 - ‖x‖) / 2) := by
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      exact lt_min (by positivity) (by linarith)
    exact hasFDerivAt_tsum_of_isPreconnected (huusum x (w.length + 1) (Vp w) hx0 hx1)
      Metric.isOpen_ball (convex_ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))).isPreconnected
      (fun m y hy => ((hTcd w m y (hsub x hx0 hx1 y hy).1).differentiableAt hone).hasFDerivAt)
      (fun m y hy => hfdbd w m x hx0 hx1 y hy) (Metric.mem_ball_self hrad0)
      (hssum w x hx0 hx1 x (Metric.mem_ball_self hrad0)) hz
  have hap : ∀ (w : List ℂ) (v : ℂ) (x : ℂ), x ≠ 0 → ‖x‖ < 1 →
      ∀ z ∈ Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)),
      fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z v
        = ∑' m : ℕ, Dw (v :: w) (Thm2Term n p A (n + m)) z := by
    as_aux_lemma =>
    intro w v x hx0 hx1 z hz
    have hS : HasSum (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z)
        (fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z) := by
      rw [(hfd w x hx0 hx1 z hz).fderiv]
      exact (hfdsum w x hx0 hx1 z hz).hasSum
    have h2 := (ContinuousLinearMap.apply ℝ ℂ v).hasSum hS
    simp only [ContinuousLinearMap.apply_apply] at h2
    have h3 : (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) z v)
        = fun m : ℕ => Dw (v :: w) (Thm2Term n p A (n + m)) z := by
      funext m
      rw [hDwcons]
    rw [h3] at h2
    exact (h2.tsum_eq).symm
  -- (13), in `Dw` form, by induction on the word
  have hDwser : ∀ (w : List ℂ) (ξ : ℂ), ξ ≠ 0 → ‖ξ‖ < 1 →
      HasSum (fun m : ℕ => Dw w (Thm2Term n p A (n + m)) ξ) (Dw w H ξ) := by
    as_aux_lemma =>
    intro w
    induction w with
    | nil =>
        intro ξ hξ hξ1
        simp only [hDwnil]
        exact hasum ξ (norm_pos_iff.mpr hξ) hξ1
    | cons v w ih =>
        intro ξ hξ hξ1
        have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        have hrad0 : (0 : ℝ) < min (‖ξ‖ / 2) ((1 - ‖ξ‖) / 2) :=
          lt_min (by positivity) (by linarith)
        have hagree : ∀ z ∈ Metric.ball ξ (min (‖ξ‖ / 2) ((1 - ‖ξ‖) / 2)),
            Dw w H z = ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) z := by
          intro z hz
          obtain ⟨hz0, hzup, hzlow⟩ := hsub ξ hξ hξ1 z hz
          exact ((ih z hz0 (by linarith)).tsum_eq).symm
        have hfe : fderiv ℝ (Dw w H) ξ
            = fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) ξ :=
          Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem
            (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrad0)) hagree)
        have hS : HasSum (fun m : ℕ => fderiv ℝ (Dw w (Thm2Term n p A (n + m))) ξ)
            (fderiv ℝ (Dw w H) ξ) := by
          rw [hfe, (hfd w ξ hξ hξ1 ξ (Metric.mem_ball_self hrad0)).fderiv]
          exact (hfdsum w ξ hξ hξ1 ξ (Metric.mem_ball_self hrad0)).hasSum
        have h2 := (ContinuousLinearMap.apply ℝ ℂ v).hasSum hS
        simp only [ContinuousLinearMap.apply_apply] at h2
        simp only [hDwcons]
        exact h2
  -- (13) itself, for the paper's `D^ν`
  have hPWser : ∀ (w : List (Fin 2)) (ξ : ℂ), ξ ≠ 0 → ‖ξ‖ < 1 →
      HasSum (fun m : ℕ => PartialWord w (Thm2Term n p A (n + m)) ξ)
        (PartialWord w H ξ) := by
    intro w ξ hξ hξ1
    simp only [PWrep]
    exact hDwser _ ξ hξ hξ1
  -- (13′) = conjunct (e): the local `C^N` statement on each ball, for every `N`
  have hContE : ContDiffOn ℝ (⊤ : ℕ∞) H ({ξ : ℂ | ‖ξ‖ < 1} \ {(0 : ℂ)}) := by
    as_aux_lemma =>
    refine contDiffOn_infty.mpr (fun N => ?_)
    refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
    have hx1 : ‖x‖ < 1 := hx.1
    have hx0 : x ≠ 0 := by
      intro h
      exact hx.2 (by rw [h]; exact Set.mem_singleton 0)
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrad0 : (0 : ℝ) < min (‖x‖ / 2) ((1 - ‖x‖) / 2) :=
      lt_min (by positivity) (by linarith)
    have hmain : ∀ (N : ℕ) (w : List ℂ),
        ContDiffOn ℝ (N : ℕ) (fun z : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) z)
          (Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2))) := by
      intro N
      induction N with
      | zero =>
          intro w
          rw [Nat.cast_zero, contDiffOn_zero]
          refine continuousOn_tsum (fun m z hz => ?_) (huusum x w.length (Vp w) hx0 hx1)
            (fun m z hz => hub w m x hx0 hx1 z hz)
          exact ((hTcd w m z (hsub x hx0 hx1 z hz).1).continuousAt).continuousWithinAt
      | succ N ih =>
          intro w
          rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = ((N : ℕ) : WithTop ℕ∞) + 1 from by
              push_cast; ring,
            contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
          refine ⟨?_, ?_, ?_⟩
          · intro z hz
            exact ((hfd w x hx0 hx1 z hz).differentiableAt).differentiableWithinAt
          · intro h
            exact absurd h (by simp)
          · refine (Θ.contDiff.comp_contDiffOn
              ((ih (1 :: w)).prodMk (ih (Complex.I :: w)))).congr ?_
            intro z hz
            refine ContinuousLinearMap.ext (fun v => ?_)
            simp only [Function.comp_apply]
            rw [hdecompCLM
                (fderiv ℝ (fun y : ℂ => ∑' m : ℕ, Dw w (Thm2Term n p A (n + m)) y) z) v,
              hap w 1 x hx0 hx1 z hz, hap w Complex.I x hx0 hx1 z hz]
            exact (hΘ (∑' m : ℕ, Dw (1 :: w) (Thm2Term n p A (n + m)) z,
              ∑' m : ℕ, Dw (Complex.I :: w) (Thm2Term n p A (n + m)) z) v).symm
    refine ⟨Metric.ball x (min (‖x‖ / 2) ((1 - ‖x‖) / 2)), Metric.isOpen_ball,
      Metric.mem_ball_self hrad0, ?_⟩
    refine ContDiffOn.mono ?_ Set.inter_subset_right
    refine (hmain N []).congr ?_
    intro z hz
    obtain ⟨hz0, hzup, hzlow⟩ := hsub x hx0 hx1 z hz
    rw [hHval z hz0 (by linarith)]
    exact tsum_congr (fun m => by rw [hDwnil])
  refine ⟨hasum, ?_, ?_, ?_, ?_⟩
  -- ## Step 7: conjunct (b).  Conjunct (a) turns `H ξ - Σ_{k ∈ Icc n j} T_k ξ` into the
  -- tail of (19) from the index `j + 1`, and on that tail (3) gives `λ_k ≥ λ_{j+1}`, so
  -- each term factors as `‖ξ‖^{λ_k} ≤ ρ^{-λ_{j+1}} ρ^{λ_k} ‖ξ‖^{λ_{j+1}}` and the
  -- constant is `2 ρ^{-λ_{j+1}} Σ_0(ρ)`, finite by (6).
  · as_aux_lemma =>
    intro ρ hρ0 hρ1 j hj
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, j = n + J := ⟨j - n, by omega⟩
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℝ, ∀ m : ℕ,
        g m = 2 * ‖A ((n : ℤ) + (m : ℤ))‖ * ρ ^ LambdaCoef n (n + m) p := ⟨_, fun _ => rfl⟩
    have hgs : Summable g := (hgeo0 ρ hρ0 hρ1).congr (fun m => (hgdef m).symm)
    have hg0 : ∀ m : ℕ, 0 ≤ g m := by
      intro m
      rw [hgdef]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hρ0.le _)
    have hρinv : (0 : ℝ) < ρ ^ (-(LambdaCoef n (j + 1) p)) := Real.rpow_pos_of_pos hρ0 _
    have hshift : Summable (fun i : ℕ => g (i + (J + 1))) :=
      (summable_nat_add_iff (J + 1)).mpr hgs
    have hb3 : ∑' i : ℕ, g (i + (J + 1)) ≤ ∑' m : ℕ, g m := by
      have he := hgs.sum_add_tsum_nat_add (J + 1)
      have hhead0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (J + 1), g i :=
        Finset.sum_nonneg (fun i _ => hg0 i)
      linarith only [he, hhead0]
    refine ⟨ρ ^ (-(LambdaCoef n (j + 1) p)) * ∑' m : ℕ, g m,
      mul_nonneg hρinv.le (tsum_nonneg hg0), ?_⟩
    intro ξ hξ hξρ
    have hξne : ξ ≠ 0 := norm_pos_iff.mp hξ
    have hξ1 : ‖ξ‖ < 1 := lt_of_le_of_lt hξρ hρ1
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ρ ^ (-(LambdaCoef n (j + 1) p))
        * ‖ξ‖ ^ LambdaCoef n (j + 1) p := ⟨_, rfl⟩
    have hc0 : (0 : ℝ) ≤ c := by
      rw [hcdef]
      exact mul_nonneg hρinv.le (Real.rpow_nonneg (norm_nonneg _) _)
    have hterm : ∀ i : ℕ, ‖Thm2Term n p A (n + (i + (J + 1))) ξ‖ ≤ c * g (i + (J + 1)) := by
      intro i
      refine le_trans (hT2 (i + (J + 1)) ξ hξne) ?_
      rw [hgdef, hcdef]
      have hk := hexpfac ρ hρ0 ‖ξ‖ hξ hξρ (LambdaCoef n (j + 1) p)
        (LambdaCoef n (n + (i + (J + 1))) p) (hLmono (j + 1) (n + (i + (J + 1))) (by omega))
      have h2A : (0 : ℝ) ≤ 2 * ‖A ((n : ℤ) + ((i + (J + 1) : ℕ) : ℤ))‖ := by positivity
      linarith only [mul_le_mul_of_nonneg_left hk h2A]
    have hsn : Summable (fun i : ℕ => ‖Thm2Term n p A (n + (i + (J + 1))) ξ‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm (hshift.mul_left c)
    have hhead : (∑ k ∈ Finset.Icc n j, Thm2Term n p A k ξ)
        = ∑ m ∈ Finset.range (J + 1), Thm2Term n p A (n + m) ξ := by
      rw [hJ]
      exact hreindexC (fun k => Thm2Term n p A k ξ) J
    have hdiff : H ξ - ∑ k ∈ Finset.Icc n j, Thm2Term n p A k ξ
        = ∑' i : ℕ, Thm2Term n p A (n + (i + (J + 1))) ξ := by
      have e1 : H ξ = (∑ m ∈ Finset.range (J + 1), Thm2Term n p A (n + m) ξ)
          + ∑' i : ℕ, Thm2Term n p A (n + (i + (J + 1))) ξ := by
        rw [← (hasum ξ hξ hξ1).tsum_eq,
          ← (hasum ξ hξ hξ1).summable.sum_add_tsum_nat_add (J + 1)]
      rw [hhead, e1]
      ring
    rw [hdiff]
    calc ‖∑' i : ℕ, Thm2Term n p A (n + (i + (J + 1))) ξ‖
        ≤ ∑' i : ℕ, ‖Thm2Term n p A (n + (i + (J + 1))) ξ‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' i : ℕ, c * g (i + (J + 1)) :=
          Summable.tsum_le_tsum hterm hsn (hshift.mul_left c)
      _ = c * ∑' i : ℕ, g (i + (J + 1)) := tsum_mul_left
      _ ≤ c * ∑' m : ℕ, g m := mul_le_mul_of_nonneg_left hb3 hc0
      _ = (ρ ^ (-(LambdaCoef n (j + 1) p)) * ∑' m : ℕ, g m)
            * ‖ξ‖ ^ LambdaCoef n (j + 1) p := by rw [hcdef]; ring
  -- ## conjunct (c): the same tail estimate for `H_r`, which is the word derivative of
  -- order one along the unit direction `ξ/‖ξ‖`, so (11) at `|w| = 1` and (13) at that
  -- same word are all that is needed.
  · as_aux_lemma =>
    intro ρ hρ0 hρ1 j hj
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, j = n + J := ⟨j - n, by omega⟩
    obtain ⟨g2, hg2def⟩ : ∃ g2 : ℕ → ℝ, ∀ i : ℕ, g2 i =
        2 * (((n : ℝ) + (i : ℝ)) * (3 + Real.sqrt (p - 1)) + 1)
          * (2 * ‖A ((n : ℤ) + (i : ℤ))‖)
          * ρ ^ (LambdaCoef n (n + i) p - 1) := ⟨_, fun _ => rfl⟩
    have hg2s : Summable g2 := by
      have h1 := (hgeo 1 ρ hρ0 hρ1).mul_left
        (4 * (3 + Real.sqrt (p - 1)) * ρ ^ (-1 : ℝ))
      have h0 := (hgeo 0 ρ hρ0 hρ1).mul_left (4 * ρ ^ (-1 : ℝ))
      refine (h1.add h0).congr (fun i => ?_)
      have he : ρ ^ (LambdaCoef n (n + i) p - 1)
          = ρ ^ (-1 : ℝ) * ρ ^ (LambdaCoef n (n + i) p) := by
        rw [← Real.rpow_add hρ0]; congr 1; ring
      rw [hg2def, he]
      simp only [pow_one, pow_zero, one_mul]
      ring
    have hg20 : ∀ i : ℕ, 0 ≤ g2 i := by
      intro i
      rw [hg2def]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hρ0.le _)
    have hρinv : (0 : ℝ) < ρ ^ (-(LambdaCoef n (j + 1) p - 1)) := Real.rpow_pos_of_pos hρ0 _
    have hshift : Summable (fun i : ℕ => g2 (i + (J + 1))) :=
      (summable_nat_add_iff (J + 1)).mpr hg2s
    have hb3 : ∑' i : ℕ, g2 (i + (J + 1)) ≤ ∑' i : ℕ, g2 i := by
      have he := hg2s.sum_add_tsum_nat_add (J + 1)
      have hhead0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (J + 1), g2 i :=
        Finset.sum_nonneg (fun i _ => hg20 i)
      linarith only [he, hhead0]
    refine ⟨ρ ^ (-(LambdaCoef n (j + 1) p - 1)) * ∑' i : ℕ, g2 i,
      mul_nonneg hρinv.le (tsum_nonneg hg20), ?_⟩
    intro ξ hξ hξρ
    have hξne : ξ ≠ 0 := norm_pos_iff.mp hξ
    have hξ1 : ‖ξ‖ < 1 := lt_of_le_of_lt hξρ hρ1
    -- `H_r` is the first-order word derivative along the unit vector `ξ/‖ξ‖`
    have hHRad : ∀ f : ℂ → ℂ, HRad f ξ = Dw [ξ / ((‖ξ‖ : ℝ) : ℂ)] f ξ := by
      intro f
      simp only [HRad, hDwcons, hDwnil]
    have hlen : (([ξ / ((‖ξ‖ : ℝ) : ℂ)] : List ℂ)).length = 1 := by simp
    have hv1 : Vp [ξ / ((‖ξ‖ : ℝ) : ℂ)] = 1 := by
      rw [hVpv]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ,
        div_self (ne_of_gt hξ)]
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ρ ^ (-(LambdaCoef n (j + 1) p - 1))
        * ‖ξ‖ ^ (LambdaCoef n (j + 1) p - 1) := ⟨_, rfl⟩
    have hc0 : (0 : ℝ) ≤ c := by
      rw [hcdef]
      exact mul_nonneg hρinv.le (Real.rpow_nonneg (norm_nonneg _) _)
    have hterm : ∀ i : ℕ, ‖HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ‖
        ≤ c * g2 (i + (J + 1)) := by
      intro i
      have hb := Trepbd [ξ / ((‖ξ‖ : ℝ) : ℂ)] (i + (J + 1)) ξ hξne
      rw [hlen, hv1] at hb
      simp only [Nat.cast_one, pow_one, mul_one] at hb
      rw [hHRad, hg2def, hcdef]
      refine le_trans hb ?_
      have hk := hexpfac ρ hρ0 ‖ξ‖ hξ hξρ (LambdaCoef n (j + 1) p - 1)
        (LambdaCoef n (n + (i + (J + 1))) p - 1)
        (by linarith only [hLmono (j + 1) (n + (i + (J + 1))) (by omega)])
      have hnn : (0 : ℝ) ≤ 2 * (((n : ℝ) + ((i + (J + 1) : ℕ) : ℝ))
            * (3 + Real.sqrt (p - 1)) + 1)
          * (2 * ‖A ((n : ℤ) + ((i + (J + 1) : ℕ) : ℤ))‖) := by positivity
      linarith only [mul_le_mul_of_nonneg_left hk hnn]
    have hsn : Summable (fun i : ℕ => ‖HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm (hshift.mul_left c)
    have hser : HasSum (fun i : ℕ => HRad (Thm2Term n p A (n + i)) ξ) (HRad H ξ) := by
      have h := hDwser [ξ / ((‖ξ‖ : ℝ) : ℂ)] ξ hξne hξ1
      simp only [← hHRad] at h
      exact h
    have hhead : (∑ k ∈ Finset.Icc n j, HRad (Thm2Term n p A k) ξ)
        = ∑ i ∈ Finset.range (J + 1), HRad (Thm2Term n p A (n + i)) ξ := by
      rw [hJ]
      exact hreindexC (fun k => HRad (Thm2Term n p A k) ξ) J
    have hdiff : HRad H ξ - ∑ k ∈ Finset.Icc n j, HRad (Thm2Term n p A k) ξ
        = ∑' i : ℕ, HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ := by
      have e1 : HRad H ξ = (∑ i ∈ Finset.range (J + 1), HRad (Thm2Term n p A (n + i)) ξ)
          + ∑' i : ℕ, HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ := by
        rw [← hser.tsum_eq, ← hser.summable.sum_add_tsum_nat_add (J + 1)]
      rw [hhead, e1]
      ring
    rw [hdiff]
    calc ‖∑' i : ℕ, HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ‖
        ≤ ∑' i : ℕ, ‖HRad (Thm2Term n p A (n + (i + (J + 1)))) ξ‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' i : ℕ, c * g2 (i + (J + 1)) :=
          Summable.tsum_le_tsum hterm hsn (hshift.mul_left c)
      _ = c * ∑' i : ℕ, g2 (i + (J + 1)) := tsum_mul_left
      _ ≤ c * ∑' i : ℕ, g2 i := mul_le_mul_of_nonneg_left hb3 hc0
      _ = (ρ ^ (-(LambdaCoef n (j + 1) p - 1)) * ∑' i : ℕ, g2 i)
            * ‖ξ‖ ^ (LambdaCoef n (j + 1) p - 1) := by rw [hcdef]; ring
  -- ## conjunct (d): with `A_n = 0` the `k = n` summand of (19) is identically zero off
  -- the origin, so every surviving index has `λ_k ≥ λ_{n+1} = γ_n`; (11) at order `m`
  -- then majorizes each word derivative, (13) sums them, and the `2^m` words are
  -- finitely many.
  · as_aux_lemma =>
    intro hA0 m ρ hρ0 hρ1
    have hDw0 : ∀ w : List ℂ, Dw w (fun _ : ℂ => (0 : ℂ)) = fun _ : ℂ => 0 := by
      intro w
      induction w with
      | nil => rw [hDwnil]
      | cons v w ih =>
          rw [hDwcons, ih]
          funext z
          simp
    have hTn0 : ∀ (w : List (Fin 2)) (ξ : ℂ), ξ ≠ 0 →
        PartialWord w (Thm2Term n p A n) ξ = 0 := by
      intro w ξ hξ
      rw [PWrep]
      have h := DwcongrOn (w.map (fun j : Fin 2 => if j = 0 then (1 : ℂ) else Complex.I))
        (Thm2Term n p A n) (fun _ : ℂ => (0 : ℂ)) {z : ℂ | z ≠ 0} isOpen_ne
        (fun z hz => by rw [hTn z hz, hA0]) ξ hξ
      rw [h, hDw0]
    obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, ∀ i : ℕ, F i =
        ((n : ℝ) + (i : ℝ)) ^ m * ‖A ((n : ℤ) + (i : ℤ))‖
          * ρ ^ (LambdaCoef n (n + i) p) := ⟨_, fun _ => rfl⟩
    have hFs : Summable F := (hgeo m ρ hρ0 hρ1).congr (fun i => (hFdef i).symm)
    have hsh : Summable (fun i : ℕ => F (i + 1)) := (summable_nat_add_iff 1).mpr hFs
    obtain ⟨h3, h3def⟩ : ∃ h3 : ℕ → ℝ, ∀ i : ℕ, h3 i =
        (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m * ρ ^ (-(m : ℝ)) * (2 * F (i + 1)) := ⟨_, fun _ => rfl⟩
    have h3s : Summable h3 :=
      (hsh.mul_left ((2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m * ρ ^ (-(m : ℝ)) * 2)).congr
        (fun i => by rw [h3def]; ring)
    have h30 : ∀ i : ℕ, 0 ≤ h3 i := by
      intro i
      rw [h3def, hFdef]
      have e1 : (0 : ℝ) ≤ (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m := by positivity
      have e2 : (0 : ℝ) ≤ ρ ^ (-(m : ℝ)) := Real.rpow_nonneg hρ0.le _
      have e3 : (0 : ℝ) ≤ ρ ^ (LambdaCoef n (n + (i + 1)) p) := Real.rpow_nonneg hρ0.le _
      exact mul_nonneg (mul_nonneg e1 e2)
        (mul_nonneg (by norm_num) (mul_nonneg (by positivity) e3))
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ρ ^ (-(GammaExp n p - (m : ℝ)))
        * ∑' i : ℕ, h3 i := ⟨_, rfl⟩
    have hD0 : (0 : ℝ) ≤ D := by
      rw [hDdef]
      exact mul_nonneg (Real.rpow_nonneg hρ0.le _) (tsum_nonneg h30)
    refine ⟨((Finset.univ : Finset (Fin m → Fin 2)).card : ℝ) * D,
      mul_nonneg (Nat.cast_nonneg _) hD0, ?_⟩
    intro ξ hξ hξρ
    have hξne : ξ ≠ 0 := norm_pos_iff.mp hξ
    have hξ1 : ‖ξ‖ < 1 := lt_of_le_of_lt hξρ hρ1
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ρ ^ (-(GammaExp n p - (m : ℝ)))
        * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := ⟨_, rfl⟩
    have hword : ∀ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        ≤ D * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
      intro v
      have hlw : (List.ofFn v).length = m := List.length_ofFn
      have hterm : ∀ i : ℕ,
          ‖PartialWord (List.ofFn v) (Thm2Term n p A (n + (i + 1))) ξ‖ ≤ c * h3 i := by
        intro i
        have hb := Televen (List.ofFn v) (i + 1) ξ hξne
        rw [hlw] at hb
        have hX1 : (1 : ℝ) ≤ ((n : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
          have h2 : (0 : ℝ) ≤ (((i + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
          linarith only [hn1, h2]
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hkey : (m : ℝ) ≤ ((n : ℝ) + ((i + 1 : ℕ) : ℝ)) * (m : ℝ) := by nlinarith only [hX1, hm0]
        have hc1 : 2 * (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) * (3 + Real.sqrt (p - 1)) + (m : ℝ)) ≤ ((n : ℝ) + ((i + 1 : ℕ) : ℝ)) * (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) := by
          linarith only [hkey]
        have hc1p : (2 * (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) * (3 + Real.sqrt (p - 1)) + (m : ℝ))) ^ m ≤ (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ m * (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m) := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hc1 _
        have hk := hexpfac ρ hρ0 ‖ξ‖ hξ hξρ (GammaExp n p - (m : ℝ))
          (LambdaCoef n (n + (i + 1)) p - (m : ℝ)) (by
            have hmo := hLmono (n + 1) (n + (i + 1)) (by omega)
            simp only [GammaExp]
            linarith only [hmo])
        have hrsplit : ρ ^ (LambdaCoef n (n + (i + 1)) p - (m : ℝ))
            = ρ ^ (-(m : ℝ)) * ρ ^ (LambdaCoef n (n + (i + 1)) p) := by
          rw [← Real.rpow_add hρ0]; congr 1; ring
        rw [h3def, hFdef, hcdef]
        refine le_trans hb ?_
        have hR0 : (0 : ℝ) ≤ (2 * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖) := by positivity
        have hS0 : (0 : ℝ) ≤ ‖ξ‖ ^ (LambdaCoef n (n + (i + 1)) p - (m : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        have hQR0 : (0 : ℝ) ≤ (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ m * (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m) * (2 * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖) := by positivity
        calc (2 * (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) * (3 + Real.sqrt (p - 1)) + (m : ℝ))) ^ m * (2 * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖) * ‖ξ‖ ^ (LambdaCoef n (n + (i + 1)) p - (m : ℝ))
            ≤ (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ m * (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m) * (2 * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖) * ‖ξ‖ ^ (LambdaCoef n (n + (i + 1)) p - (m : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1p hR0) hS0
          _ ≤ (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ m * (2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m) * (2 * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖) * ((ρ ^ (-(GammaExp n p - (m : ℝ))) * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))) * ρ ^ (LambdaCoef n (n + (i + 1)) p - (m : ℝ))) := mul_le_mul_of_nonneg_left hk hQR0
          _ = ρ ^ (-(GammaExp n p - (m : ℝ))) * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))
              * ((2 * (3 + Real.sqrt (p - 1) + (m : ℝ))) ^ m * ρ ^ (-(m : ℝ))
                  * (2 * (((n : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ m * ‖A ((n : ℤ) + ((i + 1 : ℕ) : ℤ))‖
                      * ρ ^ (LambdaCoef n (n + (i + 1)) p)))) := by rw [hrsplit]; ring
      have hsnw : Summable (fun i : ℕ =>
          ‖PartialWord (List.ofFn v) (Thm2Term n p A (n + (i + 1))) ξ‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm (h3s.mul_left c)
      have hps := hPWser (List.ofFn v) ξ hξne hξ1
      have he1 : PartialWord (List.ofFn v) H ξ
          = ∑' i : ℕ, PartialWord (List.ofFn v) (Thm2Term n p A (n + (i + 1))) ξ := by
        have hsp := hps.summable.sum_add_tsum_nat_add 1
        rw [← hps.tsum_eq, ← hsp]
        simp only [Finset.sum_range_one, Nat.add_zero]
        rw [hTn0 (List.ofFn v) ξ hξne, zero_add]
      rw [he1]
      refine le_trans (norm_tsum_le_tsum_norm hsnw) ?_
      calc ∑' i : ℕ, ‖PartialWord (List.ofFn v) (Thm2Term n p A (n + (i + 1))) ξ‖
          ≤ ∑' i : ℕ, c * h3 i := Summable.tsum_le_tsum hterm hsnw (h3s.mul_left c)
        _ = c * ∑' i : ℕ, h3 i := tsum_mul_left
        _ = D * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by rw [hcdef, hDdef]; ring
    calc ∑ v : Fin m → Fin 2, ‖PartialWord (List.ofFn v) H ξ‖
        ≤ (Finset.univ : Finset (Fin m → Fin 2)).card
            • (D * ‖ξ‖ ^ (GammaExp n p - (m : ℝ))) :=
          Finset.sum_le_card_nsmul _ _ _ (fun v _ => hword v)
      _ = ((Finset.univ : Finset (Fin m → Fin 2)).card : ℝ) * D
            * ‖ξ‖ ^ (GammaExp n p - (m : ℝ)) := by
          rw [nsmul_eq_mul]; ring
  -- ## conjunct (e) = (13′)
  · exact hContE
