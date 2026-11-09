import IwaniecManfredi.FDerivAcrossPoint
import IwaniecManfredi.PartialWord

/-- Smoothness of order `k` across the singular set.  A function which is `C^1`
on an open set, `C^∞` off a locally finite subset of it -- one meeting every
compact subset of the open set in a finite set, so that its complement is open
-- and whose partial derivatives of each order `j ≤ k` vanish at the rate
`|z - z₀|^{k+α-j}` near each point `z₀` of that subset, is `C^k` on the whole
open set.  This is the step Section 6 of the paper never states: the exponent
`d - m = k-1+α-m` of (52) is at least `α > 0` for every order `m+1 ≤ k`, so
those derivatives tend to `0` at a singular point, and `FDerivAcrossPoint`
converts that into genuine differentiability there, one order at a time.  Local
finiteness is what `paper.tex:156` supplies, the zero set being discrete there
and closed by the continuity asserted in the same sentence. -/
theorem Thm1SmoothAcrossZeros (Ω : Set ℂ) (hΩ : IsOpen Ω) (Z : Set ℂ) (hZΩ : Z ⊆ Ω)
    (hZfin : ∀ Kc ⊆ Ω, IsCompact Kc → (Z ∩ Kc).Finite)
    (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα : 0 < α)
    (w : ℂ → ℂ)
    (hw1 : ContDiffOn ℝ (1 : ℕ) w Ω)
    (hwsm : ContDiffOn ℝ (⊤ : ℕ∞) w (Ω \ Z))
    (hbd : ∀ z₀ ∈ Z, ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ → ℝ,
      ∀ (j : ℕ), 1 ≤ j → j ≤ k → ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ →
        ∑ v : Fin j → Fin 2, ‖PartialWord (List.ofFn v) w z‖
          ≤ B j * ‖z - z₀‖ ^ ((k : ℝ) + α - (j : ℝ))) :
    ContDiffOn ℝ (k : ℕ) w Ω := by
  -- ## Step 0: the two consequences of local finiteness of `Z`, from ONE construction.
  -- At any `ζ ∈ Ω` a closed ball about `ζ` lies in `Ω`, meets `Z` in a finite -- hence
  -- CLOSED -- set, and removing `ζ` from that finite set leaves a closed set missing `ζ`;
  -- the radius handed back by `Metric.isOpen_iff` on its complement is the one wanted.
  have hiso : ∀ ζ ∈ Ω, ∃ s : ℝ, 0 < s ∧ Metric.ball ζ s ⊆ Ω ∧
      ∀ z ∈ Metric.ball ζ s, z ∈ Z → z = ζ := by
    intro ζ hζ
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hΩ ζ hζ
    have hcb : Metric.closedBall ζ (ρ / 2) ⊆ Ω := by
      refine subset_trans ?_ hρsub
      intro z hz
      exact Metric.mem_ball.mpr (by linarith [Metric.mem_closedBall.mp hz])
    have hfin : ((Z ∩ Metric.closedBall ζ (ρ / 2)) \ {ζ}).Finite :=
      (hZfin _ hcb (isCompact_closedBall _ _)).subset Set.sdiff_subset
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl ζ (by simp)
    refine ⟨min ε (ρ / 2), lt_min hε (by linarith), ?_, ?_⟩
    · intro z hz
      exact hcb (Metric.mem_closedBall.mpr
        (le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))))
    · intro z hz hzZ
      have hd : dist z ζ < min ε (ρ / 2) := Metric.mem_ball.mp hz
      have h1 : z ∈ Z ∩ Metric.closedBall ζ (ρ / 2) :=
        ⟨hzZ, Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hd (min_le_right _ _)))⟩
      have h2 : z ∉ (Z ∩ Metric.closedBall ζ (ρ / 2)) \ {ζ} :=
        hεsub (Metric.mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _)))
      by_contra hne
      exact h2 ⟨h1, hne⟩
  -- (0a) `Ω - Z` is open
  have hΩZ : IsOpen (Ω \ Z) := by
    refine Metric.isOpen_iff.mpr ?_
    intro z hz
    obtain ⟨s, hs, hsub, hsiso⟩ := hiso z hz.1
    refine ⟨s, hs, fun z' hz' => ⟨hsub hz', fun hz'Z => ?_⟩⟩
    have heq : z' = z := hsiso z' hz' hz'Z
    rw [heq] at hz'Z
    exact hz.2 hz'Z
  -- ## Shared tool: the real-linear reconstruction of a map `ℂ →L[ℝ] ℂ` from its two
  -- values, as a FIXED continuous linear map of the pair.
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
    intro L v
    calc L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := by
          congr 1
          rw [Complex.real_smul, Complex.real_smul, mul_one]
          exact (Complex.re_add_im v).symm
      _ = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
          rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  -- the operator-norm bound used in (c); not a Mathlib lemma
  have hopbd : ∀ L : ℂ →L[ℝ] ℂ, ‖L‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    intro L
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [hdecompCLM L v]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [Complex.abs_re_le_norm v, Complex.abs_im_le_norm v,
      norm_nonneg (L 1), norm_nonneg (L Complex.I), abs_nonneg v.re, abs_nonneg v.im]
  -- ## Shared tools on `PartialWord`
  have hpwnil : ∀ u : ℂ → ℂ, PartialWord [] u = u := fun _ => rfl
  have hcons : ∀ (t : Fin 2) (v : List (Fin 2)) (u : ℂ → ℂ) (z : ℂ),
      PartialWord (t :: v) u z
        = fderiv ℝ (PartialWord v u) z (if t = 0 then 1 else Complex.I) :=
    fun _ _ _ _ => rfl
  have happ : ∀ (a b : List (Fin 2)) (G : ℂ → ℂ),
      PartialWord (a ++ b) G = PartialWord a (PartialWord b G) := by
    intro a b G
    simp only [PartialWord, List.foldr_append]
  have hPWcd : ∀ (v : List (Fin 2)) (G : ℂ → ℂ) (S : Set ℂ), IsOpen S →
      ContDiffOn ℝ (⊤ : ℕ∞) G S → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord v G) S := by
    intro v
    induction v with
    | nil => intro G S _ hG; exact hG
    | cons j v ih =>
        intro G S hS hG
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord v G)) S :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hS).mp (ih G S hS hG)).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  -- the FORWARD direction of the one-step bridge: a `C^{m+1}` function has `C^m` partials
  have hfwd : ∀ (u : ℂ → ℂ) (m : ℕ) (t : Fin 2), ContDiffOn ℝ ((m + 1 : ℕ)) u Ω →
      ContDiffOn ℝ (m : ℕ) (PartialWord [t] u) Ω := by
    intro u m t hu
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = ((m : ℕ) : WithTop ℕ∞) + 1 from by push_cast; ring,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ] at hu
    exact (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℂ
        (if t = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn hu.2.2
  -- ## Layer 1: the one-step bridge.  `fderiv ℝ u` is the image of the PAIR of its two
  -- partials under the fixed map `Θ`, so its `ContDiffOn` is that of the pair.
  have hbridge : ∀ (u : ℂ → ℂ) (m : ℕ), DifferentiableOn ℝ u Ω →
      ContDiffOn ℝ (m : ℕ) (PartialWord [0] u) Ω →
      ContDiffOn ℝ (m : ℕ) (PartialWord [1] u) Ω →
      ContDiffOn ℝ ((m + 1 : ℕ)) u Ω := by
    intro u m hdu h0 h1
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = ((m : ℕ) : WithTop ℕ∞) + 1 from by push_cast; ring,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hdu, fun h => absurd h (by simp), ?_⟩
    refine (Θ.contDiff.comp_contDiffOn (h0.prodMk h1)).congr ?_
    intro z hz
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [Function.comp_apply]
    have e0 : PartialWord [(0 : Fin 2)] u z = fderiv ℝ u z 1 := by
      rw [hcons, hpwnil]; simp
    have e1 : PartialWord [(1 : Fin 2)] u z = fderiv ℝ u z Complex.I := by
      rw [hcons, hpwnil]; simp
    rw [hdecompCLM (fderiv ℝ u z) v, ← e0, ← e1]
    exact (hΘ (PartialWord [(0 : Fin 2)] u z, PartialWord [(1 : Fin 2)] u z) v).symm
  -- an order-`|v|` word derivative of a `C^{|v|+m}` function is `C^m`
  have hwordlow : ∀ (v : List (Fin 2)) (m : ℕ) (u : ℂ → ℂ),
      ContDiffOn ℝ ((v.length + m : ℕ)) u Ω → ContDiffOn ℝ (m : ℕ) (PartialWord v u) Ω := by
    intro v
    induction v with
    | nil =>
        intro m u h
        rw [hpwnil]
        rw [show ([] : List (Fin 2)).length + m = m from by simp] at h
        exact h
    | cons j v ih =>
        intro m u h
        rw [show (j :: v).length + m = v.length + (m + 1) from by
          simp only [List.length_cons]; omega] at h
        have h2 := ih (m + 1) u h
        rw [show (j :: v) = [j] ++ v from rfl, happ]
        exact hfwd (PartialWord v u) m j h2
  -- ## (a)+(b)+(c)+(d): every order-`i` word derivative of `w` is `C^1` on `Ω`
  have hword1 : ∀ (i : ℕ), i + 1 ≤ k → ContDiffOn ℝ (i : ℕ) w Ω →
      ∀ v' : List (Fin 2), v'.length = i → ContDiffOn ℝ (1 : ℕ) (PartialWord v' w) Ω := by
    intro i hik hwi v' hv'
    subst hv'
    -- (a) continuity on all of `Ω`
    have ha : ContinuousOn (PartialWord v' w) Ω :=
      (hwordlow v' 0 w (by rw [Nat.add_zero]; exact hwi)).continuousOn
    -- (b) `C^∞` on the OPEN set `Ω - Z`
    have hbsm : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord v' w) (Ω \ Z) :=
      hPWcd v' w (Ω \ Z) hΩZ hwsm
    have hbdiff : ∀ z ∈ Ω \ Z, DifferentiableAt ℝ (PartialWord v' w) z := fun z hz =>
      (hbsm.differentiableOn (by simp)).differentiableAt (hΩZ.mem_nhds hz)
    have hbfd : ContinuousOn (fderiv ℝ (PartialWord v' w)) (Ω \ Z) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hΩZ).mp hbsm).2.continuousOn
    -- (c) at each point of `Z`, through `FDerivAcrossPoint`
    have hc : ∀ z₀ ∈ Z, DifferentiableAt ℝ (PartialWord v' w) z₀ ∧
        ContinuousAt (fderiv ℝ (PartialWord v' w)) z₀ := by
      intro z₀ hz₀
      obtain ⟨s, hs, hssub, hsiso⟩ := hiso z₀ (hZΩ hz₀)
      obtain ⟨δ, hδ, B, hB⟩ := hbd z₀ hz₀
      obtain ⟨r, hrdef⟩ : ∃ x : ℝ, x = min s δ := ⟨_, rfl⟩
      have hr : 0 < r := by rw [hrdef]; exact lt_min hs hδ
      have hrs : r ≤ s := by rw [hrdef]; exact min_le_left _ _
      have hrδ : r ≤ δ := by rw [hrdef]; exact min_le_right _ _
      obtain ⟨e, hedef⟩ : ∃ x : ℝ, x = (k : ℝ) + α - ((v'.length + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have he : 0 < e := by
        rw [hedef]
        have hcast : ((v'.length + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
        linarith
      -- `B (i+1) ≥ 0`, from one admissible witness point
      have hBnn : 0 ≤ B (v'.length + 1) := by
        have hzz : (z₀ + ((r / 2 : ℝ) : ℂ)) - z₀ = ((r / 2 : ℝ) : ℂ) := by ring
        have hzn : ‖(z₀ + ((r / 2 : ℝ) : ℂ)) - z₀‖ = r / 2 := by
          rw [hzz, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
        have h1 := hB (v'.length + 1) (by omega) hik (z₀ + ((r / 2 : ℝ) : ℂ))
          (by rw [hzn]; linarith) (by rw [hzn]; linarith)
        rw [hzn] at h1
        have h2 : (0 : ℝ) ≤ ∑ v : Fin (v'.length + 1) → Fin 2,
            ‖PartialWord (List.ofFn v) w (z₀ + ((r / 2 : ℝ) : ℂ))‖ :=
          Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have h3 : (0 : ℝ) < (r / 2) ^ ((k : ℝ) + α - ((v'.length + 1 : ℕ) : ℝ)) :=
          Real.rpow_pos_of_pos (by linarith) _
        have h4 : (0 : ℝ) ≤ B (v'.length + 1)
            * (r / 2) ^ ((k : ℝ) + α - ((v'.length + 1 : ℕ) : ℝ)) := le_trans h2 h1
        rcases le_or_gt 0 (B (v'.length + 1)) with hpos | hneg
        · exact hpos
        · linarith [mul_neg_of_neg_of_pos hneg h3]
      have hΩ'sub : Metric.ball z₀ r ⊆ Ω := fun z hz =>
        hssub (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) hrs))
      have hΩ'Z : ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ → z ∈ Ω \ Z := by
        intro z hz hzne
        exact ⟨hΩ'sub hz, fun hzZ => hzne (hsiso z (Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz) hrs)) hzZ)⟩
      -- the rate bound on the punctured ball, through the two words `0 :: v'`, `1 :: v'`
      have hfdbd : ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ →
          ‖fderiv ℝ (PartialWord v' w) z‖ ≤ B (v'.length + 1) * ‖z - z₀‖ ^ e := by
        intro z hz hzne
        have hzp : 0 < ‖z - z₀‖ := by
          rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzne
        have hzd : ‖z - z₀‖ < δ := by
          have hdd := Metric.mem_ball.mp hz
          rw [dist_eq_norm] at hdd
          linarith
        obtain ⟨u₀, hu₀⟩ : ∃ u : Fin (v'.length + 1) → Fin 2,
            List.ofFn u = (0 : Fin 2) :: v' := ⟨((0 : Fin 2) :: v').get, List.ofFn_get _⟩
        obtain ⟨u₁, hu₁⟩ : ∃ u : Fin (v'.length + 1) → Fin 2,
            List.ofFn u = (1 : Fin 2) :: v' := ⟨((1 : Fin 2) :: v').get, List.ofFn_get _⟩
        have hne01 : u₀ ≠ u₁ := by
          intro hcon
          have hcc : ((0 : Fin 2) :: v') = ((1 : Fin 2) :: v') := by rw [← hu₀, ← hu₁, hcon]
          simp at hcc
        have hsum := hB (v'.length + 1) (by omega) hik z hzp hzd
        have hpair : ‖PartialWord (List.ofFn u₀) w z‖ + ‖PartialWord (List.ofFn u₁) w z‖
            ≤ ∑ v : Fin (v'.length + 1) → Fin 2, ‖PartialWord (List.ofFn v) w z‖ := by
          have hps := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ ({u₀, u₁} : Finset (Fin (v'.length + 1) → Fin 2)))
            (fun x _ _ => norm_nonneg (PartialWord (List.ofFn x) w z))
          rwa [Finset.sum_pair hne01] at hps
        have hop := hopbd (fderiv ℝ (PartialWord v' w) z)
        have e0 : fderiv ℝ (PartialWord v' w) z 1 = PartialWord ((0 : Fin 2) :: v') w z := by
          rw [hcons]; simp
        have e1 : fderiv ℝ (PartialWord v' w) z Complex.I
            = PartialWord ((1 : Fin 2) :: v') w z := by
          rw [hcons]; simp
        rw [e0, e1] at hop
        rw [hu₀, hu₁] at hpair
        rw [hedef]
        linarith
      -- the derivative limit at `z₀`, by squeezing the rate bound
      have hlim : Filter.Tendsto (fun z => fderiv ℝ (PartialWord v' w) z)
          (nhdsWithin z₀ (Metric.ball z₀ r \ {z₀})) (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (g := fun z : ℂ => B (v'.length + 1) * ‖z - z₀‖ ^ e)
          (Filter.Eventually.of_forall (fun z => norm_nonneg _)) ?_ ?_
        · filter_upwards [eventually_mem_nhdsWithin] with z hz
          exact hfdbd z hz.1 (by simpa using hz.2)
        · have hnt : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖)
              (nhdsWithin z₀ (Metric.ball z₀ r \ {z₀})) (nhds 0) := by
            have hcont : ContinuousAt (fun z : ℂ => ‖z - z₀‖) z₀ :=
              (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt
            have hcw : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖)
                (nhdsWithin z₀ (Metric.ball z₀ r \ {z₀})) (nhds ‖z₀ - z₀‖) :=
              hcont.continuousWithinAt
            rw [show ‖z₀ - z₀‖ = (0 : ℝ) from by simp] at hcw
            exact hcw
          have hp : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖ ^ e)
              (nhdsWithin z₀ (Metric.ball z₀ r \ {z₀})) (nhds 0) := by
            have hrp := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.comp hnt
            rw [Real.zero_rpow (ne_of_gt he)] at hrp
            exact hrp
          simpa using hp.const_mul (B (v'.length + 1))
      have hfap := FDerivAcrossPoint (Metric.ball z₀ r) Metric.isOpen_ball z₀
        (Metric.mem_ball_self hr) (PartialWord v' w) 0
        (ha.mono hΩ'sub)
        (fun z hz => hbdiff z (hΩ'Z z hz.1 (by simpa using hz.2)))
        hlim
      exact ⟨hfap.1.differentiableAt,
        hfap.2.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))⟩
    -- (d) the two halves of `C^1` on `Ω = (Ω - Z) ∪ Z`
    rw [show ((1 : ℕ) : WithTop ℕ∞) = 0 + 1 from by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨?_, fun h => absurd h (by simp), ?_⟩
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact ((hc z hzZ).1).differentiableWithinAt
      · exact (hbdiff z ⟨hz, hzZ⟩).differentiableWithinAt
    · rw [contDiffOn_zero]
      intro z hz
      by_cases hzZ : z ∈ Z
      · exact ((hc z hzZ).2).continuousWithinAt
      · exact (hbfd.continuousAt (hΩZ.mem_nhds ⟨hz, hzZ⟩)).continuousWithinAt
  -- ## Layer 2: iterate the bridge.  `List.foldr_append` turns an order-`i` word of
  -- `∂_t u` into an order-`i+1` word of `u`.
  have hiter : ∀ (i : ℕ) (u : ℂ → ℂ), ContDiffOn ℝ (i : ℕ) u Ω →
      (∀ v' : List (Fin 2), v'.length = i → ContDiffOn ℝ (1 : ℕ) (PartialWord v' u) Ω) →
      ContDiffOn ℝ ((i + 1 : ℕ)) u Ω := by
    intro i
    induction i with
    | zero =>
        intro u _ hall
        have h := hall [] rfl
        rw [hpwnil] at h
        rw [show ((0 + 1 : ℕ) : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) from by norm_num]
        exact h
    | succ i ih =>
        intro u hu hall
        refine hbridge u (i + 1) (hu.differentiableOn (by simp)) ?_ ?_
        · refine ih (PartialWord [(0 : Fin 2)] u) (hfwd u i 0 hu) (fun v hv => ?_)
          rw [(happ v [(0 : Fin 2)] u).symm]
          exact hall (v ++ [(0 : Fin 2)]) (by simp [hv])
        · refine ih (PartialWord [(1 : Fin 2)] u) (hfwd u i 1 hu) (fun v hv => ?_)
          rw [(happ v [(1 : Fin 2)] u).symm]
          exact hall (v ++ [(1 : Fin 2)]) (by simp [hv])
  -- ## The outer induction on the order
  have main : ∀ i : ℕ, i ≤ k → ContDiffOn ℝ (i : ℕ) w Ω := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from by norm_num, contDiffOn_zero]
        exact hw1.continuousOn
    | succ i ih =>
        intro hik
        exact hiter i w (ih (by omega)) (hword1 i hik (ih (by omega)))
  exact main k le_rfl
