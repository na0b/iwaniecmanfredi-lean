import IwaniecManfredi.PartialWord
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-- A smooth function all of whose partial derivatives of order `m+1` vanish on
a connected open set is a polynomial of degree at most `m` in `z` and `conj z`
there.  This is the step Section 7 states in the words "in each case, we
conclude that `f` must be a homogeneous polynomial" (`paper.tex:630`), and the
tablet had no node producing a polynomial: `HomogPolyModFour` takes the
identity (60) as a hypothesis.  The homogeneity is supplied separately, by
(57); what is proved here is only the polynomial character, which is the part
that needs Taylor's theorem and a connectedness argument. -/
theorem VanishingDerivsIsPolynomial (U : Set ℂ) (hU : IsOpen U) (hUconn : IsConnected U)
    (m : ℕ) (g : ℂ → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hvan : ∀ w : List (Fin 2), w.length = m + 1 → ∀ z ∈ U, PartialWord w g z = 0) :
    ∃ a : ℕ → ℕ → ℂ,
      (∀ i j : ℕ, m < i + j → a i j = 0) ∧
      (∀ z ∈ U, g z = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        a i j * z ^ i * (starRingEnd ℂ z) ^ j) := by
  obtain ⟨z₀, hz₀⟩ := hUconn.nonempty
  -- ## Composition: `PartialWord` concatenates words (the word extends on the left)
  have happ : ∀ (w v : List (Fin 2)) (f : ℂ → ℂ),
      PartialWord w (PartialWord v f) = PartialWord (w ++ v) f := by
    intro w v f; simp only [PartialWord, List.foldr_append]
  -- ## An `ℝ`-linear map on `ℂ` killing both `1` and `I` is zero
  have hlin : ∀ (T : ℂ →L[ℝ] ℂ), T 1 = 0 → T Complex.I = 0 → T = 0 := by
    intro T h1 hI
    ext v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    rw [hv, map_add, map_smul, map_smul, h1, hI]; simp
  -- ## Every iterated partial of a `C^∞` function on an OPEN set is `C^∞` there
  have hPWcd : ∀ (w : List (Fin 2)) (f : ℂ → ℂ) (V : Set ℂ), IsOpen V →
      ContDiffOn ℝ (⊤ : ℕ∞) f V → ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) V := by
    intro w
    induction w with
    | nil => intro f V _ hf; exact hf
    | cons j w ih =>
        intro f V hV hf
        have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (PartialWord w f) V := ih f V hV hf
        have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (PartialWord w f)) V :=
          ((contDiffOn_infty_iff_fderiv_of_isOpen hV).mp h1).2
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.apply ℝ ℂ
            (if j = 0 then (1 : ℂ) else Complex.I))).comp_contDiffOn h2
  have hdiffat : ∀ (w : List (Fin 2)) (f : ℂ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) f U →
      ∀ z ∈ U, DifferentiableAt ℝ (PartialWord w f) z := fun w f hf z hz =>
    ((hPWcd w f U hU hf).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
  -- ## Vanishing of both length-one words is vanishing of the Fréchet derivative
  have hfd0 : ∀ (F : ℂ → ℂ),
      (∀ w : List (Fin 2), w.length = 1 → ∀ z ∈ U, PartialWord w F z = 0) →
      ∀ z ∈ U, fderiv ℝ F z = 0 := by
    intro F hw z hz
    refine hlin _ ?_ ?_
    · have := hw [0] (by simp) z hz; simpa [PartialWord] using this
    · have := hw [1] (by simp) z hz; simpa [PartialWord] using this
  -- ## THE RIGIDITY ENGINE (replaces Steps 4 and 5 of the `.tex`)
  -- If every word of length `k+1` kills `F` on `U` and every word of length `≤ k`
  -- kills `F` at the single point `z₀`, then `F ≡ 0` on `U`.  Induction on `k`:
  -- at each step the two first-order partials of `F` satisfy the hypotheses one
  -- level down, so they vanish on `U`; hence `fderiv ℝ F = 0` on `U`, hence `F`
  -- is constant on the connected open `U`, and the empty word pins that constant
  -- to `F z₀ = 0`.
  have hrigid : ∀ (k : ℕ) (F : ℂ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) F U →
      (∀ w : List (Fin 2), w.length = k + 1 → ∀ z ∈ U, PartialWord w F z = 0) →
      (∀ w : List (Fin 2), w.length ≤ k → PartialWord w F z₀ = 0) →
      ∀ z ∈ U, F z = 0 := by
    intro k
    induction k with
    | zero =>
        intro F hF hhi hlo z hz
        have hconst : F z = F z₀ :=
          hU.is_const_of_fderiv_eq_zero hUconn.isPreconnected
            (hF.differentiableOn (by norm_num)) (fun y hy => hfd0 F hhi y hy) hz hz₀
        have h0 : F z₀ = 0 := by have := hlo [] (by simp); simpa [PartialWord] using this
        rw [hconst, h0]
    | succ k ih =>
        intro F hF hhi hlo z hz
        have hstep : ∀ j : Fin 2, ∀ y ∈ U, PartialWord [j] F y = 0 := by
          intro j
          refine ih (PartialWord [j] F) (hPWcd [j] F U hU hF) ?_ ?_
          · intro w hwlen y hy
            rw [happ w [j] F]
            exact hhi (w ++ [j]) (by simp [hwlen]) y hy
          · intro w hwlen
            rw [happ w [j] F]
            exact hlo (w ++ [j]) (by simp; omega)
        have hd : ∀ y ∈ U, fderiv ℝ F y = 0 := by
          refine hfd0 F ?_
          intro w hwlen y hy
          match w with
          | [j] => exact hstep j y hy
        have hconst : F z = F z₀ :=
          hU.is_const_of_fderiv_eq_zero hUconn.isPreconnected
            (hF.differentiableOn (by norm_num)) (fun y hy => hd y hy) hz hz₀
        have h0 : F z₀ = 0 := by have := hlo [] (by simp); simpa [PartialWord] using this
        rw [hconst, h0]
  -- ## Smoothness of a polynomial in `z` and `conj z`
  have hconj : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (starRingEnd ℂ) z) :=
    Complex.conjLIE.toContinuousLinearEquiv.contDiff
  have hpolycd : ∀ b : ℕ → ℕ → ℂ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℂ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        b i j * z ^ i * (starRingEnd ℂ z) ^ j) := by
    intro b
    exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
      (contDiff_const.mul (contDiff_id.pow i)).mul (hconj.pow j)))
  -- ## `PartialWord` is additive along a difference of two `C^∞` functions on `U`
  have hsub : ∀ (G P : ℂ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) G U → ContDiffOn ℝ (⊤ : ℕ∞) P U →
      ∀ (w : List (Fin 2)), ∀ z ∈ U,
      PartialWord w (fun y => G y - P y) z = PartialWord w G z - PartialWord w P z := by
    intro G P hG hP w
    induction w with
    | nil => intro z _; rfl
    | cons j w ih =>
        intro z hz
        show fderiv ℝ (PartialWord w (fun y => G y - P y)) z
            (if j = 0 then (1 : ℂ) else Complex.I) = _
        have he : fderiv ℝ (PartialWord w (fun y => G y - P y)) z
            = fderiv ℝ (fun y => PartialWord w G y - PartialWord w P y) z :=
          Filter.EventuallyEq.fderiv_eq
            (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih y hy))
        rw [he, fderiv_fun_sub (hdiffat w G hG z hz) (hdiffat w P hP z hz)]
        rfl
  -- ## Polynomial calculus: the derivative of a monomial in `z` and `conj z`
  -- `d(z^i conj z^j)[v] = i z^(i-1) conj z^j v + j z^i conj z^(j-1) conj v`.
  have hmono : ∀ (i j : ℕ) (z v : ℂ),
      fderiv ℝ (fun y : ℂ => y ^ i * (starRingEnd ℂ y) ^ j) z v
        = (i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j * v
          + (j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1) * (starRingEnd ℂ v) := by
    intro i j z v
    have hcA : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℂ => y ^ i) := contDiff_id.pow i
    have hcB : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℂ => (starRingEnd ℂ y) ^ j) := hconj.pow j
    have hdA : DifferentiableAt ℝ (fun y : ℂ => y ^ i) z := hcA.differentiable (by norm_num) z
    have hdB : DifferentiableAt ℝ (fun y : ℂ => (starRingEnd ℂ y) ^ j) z :=
      hcB.differentiable (by norm_num) z
    have hA : fderiv ℝ (fun y : ℂ => y ^ i) z v = (i : ℂ) * z ^ (i - 1) * v := by
      have h := (hasDerivAt_pow i z).hasFDerivAt.restrictScalars ℝ
      rw [h.fderiv]; simp [mul_comm]
    have hcj : HasFDerivAt (fun y : ℂ => (starRingEnd ℂ) y)
        (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) z :=
      (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ).hasFDerivAt
    have hp := (hasDerivAt_pow j (starRingEnd ℂ z)).hasFDerivAt.restrictScalars ℝ
    have hB : fderiv ℝ (fun y : ℂ => (starRingEnd ℂ y) ^ j) z v
        = (j : ℂ) * (starRingEnd ℂ z) ^ (j - 1) * (starRingEnd ℂ v) := by
      have h : HasFDerivAt (fun y : ℂ => (starRingEnd ℂ y) ^ j)
          ((ContinuousLinearMap.restrictScalars ℝ
              (ContinuousLinearMap.toSpanSingleton ℂ
                ((j : ℂ) * (starRingEnd ℂ z) ^ (j - 1)))).comp
            (Complex.conjLIE.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ)) z := hp.comp z hcj
      rw [h.fderiv]; simp [mul_comm]
    rw [fderiv_fun_mul hdA hdB]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hA, hB]; ring
  have hmd : ∀ (c : ℂ) (i j : ℕ) (z : ℂ),
      DifferentiableAt ℝ (fun y : ℂ => c * y ^ i * (starRingEnd ℂ y) ^ j) z := fun c i j z =>
    ((contDiff_const.mul (contDiff_id.pow i)).mul (hconj.pow j)).differentiable (by norm_num) z
  -- ## The same, for a whole coefficient family
  have hsumfd : ∀ (b : ℕ → ℕ → ℂ) (z v : ℂ),
      fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * y ^ i * (starRingEnd ℂ y) ^ j) z v
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (b i j * ((i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j * v
              + (j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1) * (starRingEnd ℂ v))) := by
    intro b z v
    rw [fderiv_fun_sum
      (A := fun i (y : ℂ) => ∑ j ∈ Finset.range (m + 1),
        b i j * y ^ i * (starRingEnd ℂ y) ^ j)
      (fun i _ => DifferentiableAt.fun_sum (fun j _ => hmd (b i j) i j z))]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_fun_sum
      (A := fun j (y : ℂ) => b i j * y ^ i * (starRingEnd ℂ y) ^ j)
      (fun j _ => hmd (b i j) i j z)]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hceq : (fun y : ℂ => b i j * y ^ i * (starRingEnd ℂ y) ^ j)
        = fun y : ℂ => b i j * (y ^ i * (starRingEnd ℂ y) ^ j) := by funext y; ring
    have hdm2 : DifferentiableAt ℝ (fun y : ℂ => y ^ i * (starRingEnd ℂ y) ^ j) z :=
      ((contDiff_id.pow i).mul (hconj.pow j)).differentiable (by norm_num) z
    rw [hceq, fderiv_const_mul hdm2]
    simp only [smul_apply, smul_eq_mul]
    rw [hmono i j z v]
  -- ## The two index shifts.  Factor the untouched sum out first, then ONE
  -- `Finset.sum_range_succ'`; the boundary term it leaves carries the
  -- out-of-range coefficient, which the degree bound kills.
  have hS1 : ∀ (b : ℕ → ℕ → ℂ) (z : ℂ), (∀ β, b (m + 1) β = 0) →
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * ((i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j)
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (((i : ℂ) + 1) * b (i + 1) j) * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro b z hbN
    set f : ℕ → ℂ := fun i => ∑ j ∈ Finset.range (m + 1), b i j * (starRingEnd ℂ z) ^ j with hf
    have hL : ∀ i : ℕ, (∑ j ∈ Finset.range (m + 1),
        b i j * ((i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j))
        = (i : ℂ) * z ^ (i - 1) * f i := by
      intro i; rw [hf, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hR : ∀ i : ℕ, (∑ j ∈ Finset.range (m + 1),
        (((i : ℂ) + 1) * b (i + 1) j) * z ^ i * (starRingEnd ℂ z) ^ j)
        = ((i : ℂ) + 1) * z ^ i * f (i + 1) := by
      intro i; rw [hf, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i),
      Finset.sum_range_succ' (fun i => (i : ℂ) * z ^ (i - 1) * f i) m,
      Finset.sum_range_succ (fun i => ((i : ℂ) + 1) * z ^ i * f (i + 1)) m]
    have hfN : f (m + 1) = 0 := by
      rw [hf]; simp only
      exact Finset.sum_eq_zero (fun j _ => by rw [hbN j]; ring)
    rw [hfN]
    simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast; ring_nf
  have hS2 : ∀ (b : ℕ → ℕ → ℂ) (z : ℂ), (∀ α, b α (m + 1) = 0) →
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * ((j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1))
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (((j : ℂ) + 1) * b i (j + 1)) * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro b z hbN
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hL : (∑ j ∈ Finset.range (m + 1),
        b i j * ((j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1)))
        = z ^ i * ∑ j ∈ Finset.range (m + 1),
            ((j : ℂ) * (starRingEnd ℂ z) ^ (j - 1) * b i j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have hR : (∑ j ∈ Finset.range (m + 1),
        (((j : ℂ) + 1) * b i (j + 1)) * z ^ i * (starRingEnd ℂ z) ^ j)
        = z ^ i * ∑ j ∈ Finset.range (m + 1),
            (((j : ℂ) + 1) * (starRingEnd ℂ z) ^ j * b i (j + 1)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hL, hR]
    congr 1
    rw [Finset.sum_range_succ' (fun j => (j : ℂ) * (starRingEnd ℂ z) ^ (j - 1) * b i j) m,
      Finset.sum_range_succ (fun j => ((j : ℂ) + 1) * (starRingEnd ℂ z) ^ j * b i (j + 1)) m,
      hbN i]
    simp only [Nat.cast_zero, zero_mul, add_zero, mul_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring_nf
  -- ## One partial derivative of a polynomial is a polynomial of one lower degree
  have hshift : ∀ (j0 : Fin 2) (b : ℕ → ℕ → ℂ),
      (∀ β, b (m + 1) β = 0) → (∀ α, b α (m + 1) = 0) →
      ∀ z : ℂ, PartialWord [j0] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          ((if j0 = 0 then (1 : ℂ) else Complex.I) * (((i : ℂ) + 1) * b (i + 1) j)
            + (starRingEnd ℂ (if j0 = 0 then (1 : ℂ) else Complex.I))
                * (((j : ℂ) + 1) * b i (j + 1)))
            * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro j0 b hb1 hb2 z
    show fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        (if j0 = 0 then (1 : ℂ) else Complex.I) = _
    set v : ℂ := (if j0 = 0 then (1 : ℂ) else Complex.I) with hv
    rw [hsumfd b z v]
    have hsplit : ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (b i j * ((i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j * v
            + (j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1) * (starRingEnd ℂ v)))
        = v * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              b i j * ((i : ℂ) * z ^ (i - 1) * (starRingEnd ℂ z) ^ j))
          + (starRingEnd ℂ v) * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              b i j * ((j : ℂ) * z ^ i * (starRingEnd ℂ z) ^ (j - 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit, hS1 b z hb1, hS2 b z hb2, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- ## A polynomial supported at the origin alone is that constant
  have hcollapse : ∀ (b : ℕ → ℕ → ℂ), (∀ i j, 0 < i + j → b i j = 0) → ∀ z : ℂ,
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        b i j * z ^ i * (starRingEnd ℂ z) ^ j) = b 0 0 := by
    intro b hb z
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_]
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_]
      · simp
      · intro j' _ hj'
        rw [hb 0 j' (by omega)]; ring
    · intro i' _ hi'
      refine Finset.sum_eq_zero (fun j' _ => ?_)
      rw [hb i' j' (by omega)]; ring
  -- ## `P` is additive and subtractive in the coefficient family
  have hPadd : ∀ (b1 b2 : ℕ → ℕ → ℂ) (z : ℂ),
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (b1 i j + b2 i j) * z ^ i * (starRingEnd ℂ z) ^ j)
      = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b1 i j * z ^ i * (starRingEnd ℂ z) ^ j)
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b2 i j * z ^ i * (starRingEnd ℂ z) ^ j) := by
    intro b1 b2 z
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hPsub : ∀ (b1 b2 : ℕ → ℕ → ℂ) (z : ℂ),
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (b1 i j - b2 i j) * z ^ i * (starRingEnd ℂ z) ^ j)
      = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b1 i j * z ^ i * (starRingEnd ℂ z) ^ j)
        - (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b2 i j * z ^ i * (starRingEnd ℂ z) ^ j) := by
    intro b1 b2 z
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- ## Mixed-partial symmetry, in `PartialWord` form
  have hswap2 : ∀ (f : ℂ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) f U → ∀ (j k : Fin 2), ∀ z ∈ U,
      PartialWord [j, k] f z = PartialWord [k, j] f z := by
    intro f hf j k z hz
    have hca : ContDiffAt ℝ (⊤ : ℕ∞) f z := hf.contDiffAt (hU.mem_nhds hz)
    have hsym : IsSymmSndFDerivAt ℝ f z := by
      refine hca.isSymmSndFDerivAt ?_
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top
    have hdf : DifferentiableAt ℝ (fderiv ℝ f) z := by
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf).2
      exact (h2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
    have key : ∀ a b : ℂ, fderiv ℝ (fun y : ℂ => fderiv ℝ f y b) z a
        = fderiv ℝ (fderiv ℝ f) z a b := by
      intro a b
      have h1 : HasFDerivAt (fun y : ℂ => fderiv ℝ f y b)
          ((ContinuousLinearMap.apply ℝ ℂ b).comp (fderiv ℝ (fderiv ℝ f) z)) z :=
        (ContinuousLinearMap.apply ℝ ℂ b).hasFDerivAt.comp z hdf.hasFDerivAt
      rw [h1.fderiv]
      rfl
    show fderiv ℝ (fun y : ℂ => fderiv ℝ f y (if k = 0 then (1:ℂ) else Complex.I)) z
        (if j = 0 then (1:ℂ) else Complex.I)
      = fderiv ℝ (fun y : ℂ => fderiv ℝ f y (if j = 0 then (1:ℂ) else Complex.I)) z
        (if k = 0 then (1:ℂ) else Complex.I)
    rw [key, key, hsym.eq]
  -- ## POLYNOMIAL RIGIDITY: the coefficient family of a polynomial vanishing on `U`
  -- is zero.  The two Wirtinger shifts are diagonal, which is what makes the
  -- induction on the degree bound go through in the `z`, `conj z` basis.
  have hvan1 : ∀ (b : ℕ → ℕ → ℂ),
      (∀ z ∈ U, (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * z ^ i * (starRingEnd ℂ z) ^ j) = 0) →
      ∀ (j0 : Fin 2), ∀ z ∈ U, PartialWord [j0] (fun y : ℂ =>
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * y ^ i * (starRingEnd ℂ y) ^ j) z = 0 := by
    intro b hb j0 z hz
    show fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        (if j0 = 0 then (1 : ℂ) else Complex.I) = 0
    have he : fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z :=
      Filter.EventuallyEq.fderiv_eq
        (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => hb y hy))
    rw [he]; simp
  -- RIGIDITY, by induction on the degree bound
  have hrig : ∀ (d : ℕ), d ≤ m → ∀ (b : ℕ → ℕ → ℂ), (∀ i j, d < i + j → b i j = 0) →
      (∀ z ∈ U, (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * z ^ i * (starRingEnd ℂ z) ^ j) = 0) →
      ∀ i j, b i j = 0 := by
    intro d
    induction d with
    | zero =>
        intro _ b hb hz i j
        rcases Nat.eq_zero_or_pos (i + j) with h | h
        · -- only b 0 0 survives; evaluate the sum at z₀
          have hi : i = 0 := by omega
          have hj : j = 0 := by omega
          subst hi; subst hj
          have h0 := hz z₀ hz₀
          rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_] at h0
          · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_] at h0
            · simpa using h0
            · intro j' _ hj'
              rw [hb 0 j' (by omega)]; ring
          · intro i' _ hi'
            refine Finset.sum_eq_zero (fun j' _ => ?_)
            rw [hb i' j' (by omega)]; ring
        · exact hb i j (by omega)
    | succ d ih =>
        intro hdm b hb hz
        have hbd1 : ∀ β, b (m + 1) β = 0 := fun β => hb (m + 1) β (by omega)
        have hbd2 : ∀ α, b α (m + 1) = 0 := fun α => hb α (m + 1) (by omega)
        -- the two Wirtinger combinations of the j0 = 0 and j0 = 1 shifts
        have e0 : (if (0 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = 1 := by norm_num
        have e1 : (if (1 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = Complex.I := by
          norm_num
        have hI : ∀ i j : ℕ, ((i : ℂ) + 1) * b (i + 1) j = 0 := by
          have key : ∀ z ∈ U, (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (((i : ℂ) + 1) * b (i + 1) j) * z ^ i * (starRingEnd ℂ z) ^ j) = 0 := by
            intro z hz'
            have h0 := hvan1 b hz 0 z hz'
            have h1 := hvan1 b hz 1 z hz'
            rw [hshift 0 b hbd1 hbd2 z, e0, map_one] at h0
            rw [hshift 1 b hbd1 hbd2 z, e1, Complex.conj_I] at h1
            -- the Wirtinger combination (d0 - I d1)/2 picks out the i-shift alone
            have hcomb : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                (((i : ℂ) + 1) * b (i + 1) j) * z ^ i * (starRingEnd ℂ z) ^ j) * 2
                = ((∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                      ((1 : ℂ) * (((i : ℂ) + 1) * b (i + 1) j)
                        + (1 : ℂ) * (((j : ℂ) + 1) * b i (j + 1)))
                      * z ^ i * (starRingEnd ℂ z) ^ j)
                  - Complex.I * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                      (Complex.I * (((i : ℂ) + 1) * b (i + 1) j)
                        + (-Complex.I) * (((j : ℂ) + 1) * b i (j + 1)))
                      * z ^ i * (starRingEnd ℂ z) ^ j)) := by
              simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              have hII : Complex.I * Complex.I = -1 := by simp
              linear_combination ((((i : ℂ) + 1) * b (i + 1) j
                - ((j : ℂ) + 1) * b i (j + 1)) * z ^ i * (starRingEnd ℂ z) ^ j) * hII
            rw [h0, h1] at hcomb
            simpa using hcomb
          intro i j
          exact ih (by omega) (fun α β => ((α : ℂ) + 1) * b (α + 1) β)
            (fun α β hαβ => by rw [hb (α + 1) β (by omega)]; ring) key i j
        have hJ : ∀ i j : ℕ, ((j : ℂ) + 1) * b i (j + 1) = 0 := by
          have key : ∀ z ∈ U, (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (((j : ℂ) + 1) * b i (j + 1)) * z ^ i * (starRingEnd ℂ z) ^ j) = 0 := by
            intro z hz'
            have h0 := hvan1 b hz 0 z hz'
            have h1 := hvan1 b hz 1 z hz'
            rw [hshift 0 b hbd1 hbd2 z, e0, map_one] at h0
            rw [hshift 1 b hbd1 hbd2 z, e1, Complex.conj_I] at h1
            have hcomb : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                (((j : ℂ) + 1) * b i (j + 1)) * z ^ i * (starRingEnd ℂ z) ^ j) * 2
                = ((∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                      ((1 : ℂ) * (((i : ℂ) + 1) * b (i + 1) j)
                        + (1 : ℂ) * (((j : ℂ) + 1) * b i (j + 1)))
                      * z ^ i * (starRingEnd ℂ z) ^ j)
                  + Complex.I * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
                      (Complex.I * (((i : ℂ) + 1) * b (i + 1) j)
                        + (-Complex.I) * (((j : ℂ) + 1) * b i (j + 1)))
                      * z ^ i * (starRingEnd ℂ z) ^ j)) := by
              simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              have hII : Complex.I * Complex.I = -1 := by simp
              linear_combination ((((j : ℂ) + 1) * b i (j + 1)
                - ((i : ℂ) + 1) * b (i + 1) j) * z ^ i * (starRingEnd ℂ z) ^ j) * hII
            rw [h0, h1] at hcomb
            simpa using hcomb
          intro i j
          exact ih (by omega) (fun α β => ((β : ℂ) + 1) * b α (β + 1))
            (fun α β hαβ => by rw [hb α (β + 1) (by omega)]; ring) key i j
        intro i j
        rcases Nat.eq_zero_or_pos i with hi | hi
        · rcases Nat.eq_zero_or_pos j with hj | hj
          · -- b 0 0: evaluate the sum at z₀, every other term already killed
            subst hi; subst hj
            have h0 := hz z₀ hz₀
            rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_] at h0
            · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_] at h0
              · simpa using h0
              · intro j' _ hj'
                obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
                have hne : ((j'' : ℂ) + 1) ≠ 0 := by
                  have h : ((j'' + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j'')
                  push_cast at h; exact h
                rw [(mul_eq_zero.mp (hJ 0 j'')).resolve_left hne]; ring
            · intro i' _ hi'
              refine Finset.sum_eq_zero (fun j' _ => ?_)
              obtain ⟨i'', rfl⟩ : ∃ i'', i' = i'' + 1 := ⟨i' - 1, by omega⟩
              have hne : ((i'' : ℂ) + 1) ≠ 0 := by
                have h : ((i'' + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i'')
                push_cast at h; exact h
              rw [(mul_eq_zero.mp (hI i'' j')).resolve_left hne]; ring
          · subst hi
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            have hne : ((j' : ℂ) + 1) ≠ 0 := by
              have h : ((j' + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j')
              push_cast at h; exact h
            exact (mul_eq_zero.mp (hJ 0 j')).resolve_left hne
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          have hne : ((i' : ℂ) + 1) ≠ 0 := by
            have h : ((i' + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i')
            push_cast at h; exact h
          exact (mul_eq_zero.mp (hI i' j)).resolve_left hne
  -- ## Reading `hshift` off at the two directions.  At `j0 = 0` (`v = 1`,
  -- `conj v = 1`) the coefficients of `∂₀ P b` are `D b + Dbar b`; at `j0 = 1`
  -- (`v = I`, `conj v = -I`) the coefficients of `∂₁ P b` are `I(D b - Dbar b)`,
  -- where `D b i j = (i+1) b (i+1) j` and `Dbar b i j = (j+1) b i (j+1)` are the
  -- coefficient actions of the two Wirtinger operators.
  have e0 : (if (0 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = 1 := by norm_num
  have e1 : (if (1 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = Complex.I := by norm_num
  have hA : ∀ (b : ℕ → ℕ → ℂ), (∀ β, b (m + 1) β = 0) → (∀ α, b α (m + 1) = 0) →
      ∀ z : ℂ, PartialWord [0] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (((i : ℂ) + 1) * b (i + 1) j + ((j : ℂ) + 1) * b i (j + 1))
            * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro b hb1 hb2 z
    rw [hshift 0 b hb1 hb2 z, e0, map_one]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hB : ∀ (b : ℕ → ℕ → ℂ), (∀ β, b (m + 1) β = 0) → (∀ α, b α (m + 1) = 0) →
      ∀ z : ℂ, PartialWord [1] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z
        = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (Complex.I * (((i : ℂ) + 1) * b (i + 1) j)
            - Complex.I * (((j : ℂ) + 1) * b i (j + 1)))
            * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro b hb1 hb2 z
    rw [hshift 1 b hb1 hb2 z, e1, Complex.conj_I]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  -- ## PINNING.  `hrigid` at `k = 0` turns "both first partials agree on `U` and
  -- the values agree at `z₀`" into "the functions agree on `U`".  This is why
  -- `hrigid` and `hsub` stay in use rather than becoming dead code.
  have hpin : ∀ (G : ℂ → ℂ) (b : ℕ → ℕ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) G U →
      (∀ j0 : Fin 2, ∀ z ∈ U, PartialWord [j0] G z
          = PartialWord [j0] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
              ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z) →
      G z₀ = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * z₀ ^ i * (starRingEnd ℂ z₀) ^ j) →
      ∀ z ∈ U, G z = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro G b hG hd hz0
    have hPcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) U :=
      (hpolycd b).contDiffOn
    have hF : ∀ z ∈ U, (fun y : ℂ => G y - ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) z = 0 := by
      refine hrigid 0 _ (hG.sub hPcd) ?_ ?_
      · intro w hwlen y hy
        rw [hsub G (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1), b i j * y ^ i * (starRingEnd ℂ y) ^ j) hG hPcd w y hy]
        match w with
        | [j0] => rw [hd j0 y hy]; ring
      · intro w hwlen
        match w with
        | [] =>
            show G z₀ - (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              b i j * z₀ ^ i * (starRingEnd ℂ z₀) ^ j) = 0
            rw [hz0]; ring
    intro z hz
    have h := hF z hz
    simp only at h
    linear_combination h
  have hII : Complex.I * Complex.I = -1 := by simp
  -- ## THE INDUCTION.  For every `d ≤ m`, a function killed on `U` by every word
  -- of length `d+1` is a polynomial of degree `≤ d` on `U`.  The step integrates
  -- the two first-order partials in the `z`, `conj z` basis, where the Wirtinger
  -- coefficient actions `D` and `Dbar` are diagonal; the compatibility of the two
  -- antiderivatives is where mixed symmetry (`hswap2`) and rigidity (`hrig`) are
  -- used, and nowhere else.
  have hClaim : ∀ d : ℕ, d ≤ m → ∀ G : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) G U →
      (∀ w : List (Fin 2), w.length = d + 1 → ∀ z ∈ U, PartialWord w G z = 0) →
      ∃ b : ℕ → ℕ → ℂ, (∀ i j, d < i + j → b i j = 0) ∧
        ∀ z ∈ U, G z = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          b i j * z ^ i * (starRingEnd ℂ z) ^ j := by
    intro d
    induction d with
    | zero =>
        intro _ G hG hw
        refine ⟨fun i j => if i = 0 ∧ j = 0 then G z₀ else 0, ?_, ?_⟩
        · intro i j hij
          have : ¬ (i = 0 ∧ j = 0) := by omega
          simp only [this, if_false]
        · have hsupp : ∀ i j : ℕ, 0 < i + j →
              (if i = 0 ∧ j = 0 then G z₀ else 0) = 0 := by
            intro i j hij
            have : ¬ (i = 0 ∧ j = 0) := by omega
            simp only [this, if_false]
          refine hpin G _ hG ?_ ?_
          · intro j0 z hz
            have hL : PartialWord [j0] G z = 0 := hw [j0] (by simp) z hz
            have hb1 : ∀ β : ℕ, (if m + 1 = 0 ∧ β = 0 then G z₀ else 0) = 0 :=
              fun β => hsupp (m + 1) β (by omega)
            have hb2 : ∀ α : ℕ, (if α = 0 ∧ m + 1 = 0 then G z₀ else 0) = 0 :=
              fun α => hsupp α (m + 1) (by omega)
            rw [hL]
            match j0 with
            | 0 =>
                rw [hA _ hb1 hb2 z]
                refine (Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero
                  (fun j _ => ?_))).symm
                rw [hsupp (i + 1) j (by omega), hsupp i (j + 1) (by omega)]; ring
            | 1 =>
                rw [hB _ hb1 hb2 z]
                refine (Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero
                  (fun j _ => ?_))).symm
                rw [hsupp (i + 1) j (by omega), hsupp i (j + 1) (by omega)]; ring
          · rw [hcollapse _ hsupp z₀]
            simp
    | succ d ih =>
        intro hdm G hG hw
        -- the two first-order partials satisfy the hypotheses one level down
        have hFw : ∀ (j0 : Fin 2) (w : List (Fin 2)), w.length = d + 1 → ∀ z ∈ U,
            PartialWord w (PartialWord [j0] G) z = 0 := by
          intro j0 w hwlen z hz
          rw [happ w [j0] G]
          exact hw (w ++ [j0]) (by simp [hwlen]) z hz
        obtain ⟨c0, hc0s, hc0⟩ :=
          ih (by omega) (PartialWord [0] G) (hPWcd [0] G U hU hG) (hFw 0)
        obtain ⟨c1, hc1s, hc1⟩ :=
          ih (by omega) (PartialWord [1] G) (hPWcd [1] G U hU hG) (hFw 1)
        have hb0 : ∀ β, c0 (m + 1) β = 0 := fun β => hc0s (m + 1) β (by omega)
        have hb0' : ∀ α, c0 α (m + 1) = 0 := fun α => hc0s α (m + 1) (by omega)
        have hb1 : ∀ β, c1 (m + 1) β = 0 := fun β => hc1s (m + 1) β (by omega)
        have hb1' : ∀ α, c1 α (m + 1) = 0 := fun α => hc1s α (m + 1) (by omega)
        -- COMPATIBILITY: `B c0 = A c1`, the only use of `hswap2` and `hrig`
        have hcompat : ∀ i j : ℕ,
            Complex.I * (((i : ℂ) + 1) * c0 (i + 1) j)
              - Complex.I * (((j : ℂ) + 1) * c0 i (j + 1))
            = ((i : ℂ) + 1) * c1 (i + 1) j + ((j : ℂ) + 1) * c1 i (j + 1) := by
          have hdiffs : ∀ i j : ℕ, d < i + j →
              (Complex.I * (((i : ℂ) + 1) * c0 (i + 1) j)
                - Complex.I * (((j : ℂ) + 1) * c0 i (j + 1)))
              - (((i : ℂ) + 1) * c1 (i + 1) j + ((j : ℂ) + 1) * c1 i (j + 1)) = 0 := by
            intro i j hij
            rw [hc0s (i + 1) j (by omega), hc0s i (j + 1) (by omega),
              hc1s (i + 1) j (by omega), hc1s i (j + 1) (by omega)]
            ring
          have hvanish : ∀ z ∈ U, (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              ((Complex.I * (((i : ℂ) + 1) * c0 (i + 1) j)
                  - Complex.I * (((j : ℂ) + 1) * c0 i (j + 1)))
                - (((i : ℂ) + 1) * c1 (i + 1) j + ((j : ℂ) + 1) * c1 i (j + 1)))
                * z ^ i * (starRingEnd ℂ z) ^ j) = 0 := by
            intro z hz
            rw [hPsub (fun i j => Complex.I * (((i : ℂ) + 1) * c0 (i + 1) j)
                  - Complex.I * (((j : ℂ) + 1) * c0 i (j + 1)))
                (fun i j => ((i : ℂ) + 1) * c1 (i + 1) j + ((j : ℂ) + 1) * c1 i (j + 1)) z,
              ← hB c0 hb0 hb0' z, ← hA c1 hb1 hb1' z]
            -- transport each along `hc0` / `hc1`, which hold on the open `U`
            have hf0 : PartialWord [1] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
                ∑ j ∈ Finset.range (m + 1), c0 i j * y ^ i * (starRingEnd ℂ y) ^ j) z
                = PartialWord [1] (PartialWord [0] G) z := by
              show fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
                  ∑ j ∈ Finset.range (m + 1), c0 i j * y ^ i * (starRingEnd ℂ y) ^ j) z
                  (if (1 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = _
              rw [Filter.EventuallyEq.fderiv_eq
                (Filter.eventuallyEq_of_mem (hU.mem_nhds hz)
                  (fun y hy => (hc0 y hy).symm))]
              rfl
            have hf1 : PartialWord [0] (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
                ∑ j ∈ Finset.range (m + 1), c1 i j * y ^ i * (starRingEnd ℂ y) ^ j) z
                = PartialWord [0] (PartialWord [1] G) z := by
              show fderiv ℝ (fun y : ℂ => ∑ i ∈ Finset.range (m + 1),
                  ∑ j ∈ Finset.range (m + 1), c1 i j * y ^ i * (starRingEnd ℂ y) ^ j) z
                  (if (0 : Fin 2) = 0 then (1 : ℂ) else Complex.I) = _
              rw [Filter.EventuallyEq.fderiv_eq
                (Filter.eventuallyEq_of_mem (hU.mem_nhds hz)
                  (fun y hy => (hc1 y hy).symm))]
              rfl
            rw [hf0, hf1, happ [1] [0] G, happ [0] [1] G]
            show PartialWord [1, 0] G z - PartialWord [0, 1] G z = 0
            rw [hswap2 G hG 1 0 z hz]
            ring
          intro i j
          have := hrig d (by omega) _ hdiffs hvanish i j
          linear_combination this
        -- the two antiderivative targets
        have huv : ∀ i j : ℕ,
            ((j : ℂ) + 1) * ((c0 i (j + 1) - Complex.I * c1 i (j + 1)) / 2)
              = ((i : ℂ) + 1) * ((c0 (i + 1) j + Complex.I * c1 (i + 1) j) / 2) := by
          intro i j
          linear_combination (Complex.I / 2) * hcompat i j
            + ((((j : ℂ) + 1) * c0 i (j + 1) - ((i : ℂ) + 1) * c0 (i + 1) j) / 2) * hII
        -- the antiderivative, with the index shift in ARGUMENT position only
        obtain ⟨a0, ha0⟩ : ∃ f : ℕ → ℕ → ℂ, f = fun i j =>
            if i = 0 then (if j = 0 then 0
              else (c0 0 (j - 1) + Complex.I * c1 0 (j - 1)) / 2 / (j : ℂ))
            else (c0 (i - 1) j - Complex.I * c1 (i - 1) j) / 2 / (i : ℂ) := ⟨_, rfl⟩
        have hane : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := by
          intro k
          have h : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
          push_cast at h; exact h
        have hD : ∀ i j : ℕ, ((i : ℂ) + 1) * a0 (i + 1) j
            = (c0 i j - Complex.I * c1 i j) / 2 := by
          intro i j
          rw [ha0]
          simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          push_cast
          field_simp
        have hDbar : ∀ i j : ℕ, ((j : ℂ) + 1) * a0 i (j + 1)
            = (c0 i j + Complex.I * c1 i j) / 2 := by
          intro i j
          rcases Nat.eq_zero_or_pos i with hi | hi
          · subst hi
            rw [ha0]
            simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
            push_cast
            field_simp
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            rw [ha0]
            simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
            push_cast
            have hi1 : ((i' : ℂ) + 1) ≠ 0 := hane i'
            field_simp
            linear_combination 2 * huv i' j
        -- values of `a0` at the three index shapes
        have ha0s : ∀ i j : ℕ, d + 1 < i + j → a0 i j = 0 := by
          intro i j hij
          rw [ha0]
          rcases Nat.eq_zero_or_pos i with hi | hi
          · subst hi
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
            rw [hc0s 0 j' (by omega), hc1s 0 j' (by omega)]
            simp
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
            rw [hc0s i' j (by omega), hc1s i' j (by omega)]
            simp
        -- absorb the constant into the `(0,0)` coefficient, which `D` and `Dbar`
        -- never read
        obtain ⟨C, hC⟩ : ∃ c : ℂ, c = G z₀ - (∑ i ∈ Finset.range (m + 1),
            ∑ j ∈ Finset.range (m + 1), a0 i j * z₀ ^ i * (starRingEnd ℂ z₀) ^ j) :=
          ⟨_, rfl⟩
        refine ⟨fun i j => a0 i j + (if i = 0 ∧ j = 0 then C else 0), ?_, ?_⟩
        · intro i j hij
          have hne : ¬ (i = 0 ∧ j = 0) := by omega
          simp only [hne, if_false, add_zero]
          exact ha0s i j hij
        · have hdel : ∀ i j : ℕ, 0 < i + j → (if i = 0 ∧ j = 0 then C else 0) = 0 := by
            intro i j hij
            have hne : ¬ (i = 0 ∧ j = 0) := by omega
            simp only [hne, if_false]
          have haval : ∀ i j : ℕ, (a0 i j + (if i = 0 ∧ j = 0 then C else 0))
              = a0 i j + (if i = 0 ∧ j = 0 then C else 0) := fun _ _ => rfl
          have habd1 : ∀ β : ℕ, (a0 (m + 1) β + (if m + 1 = 0 ∧ β = 0 then C else 0)) = 0 := by
            intro β
            rw [hdel (m + 1) β (by omega), ha0s (m + 1) β (by omega)]; ring
          have habd2 : ∀ α : ℕ, (a0 α (m + 1) + (if α = 0 ∧ m + 1 = 0 then C else 0)) = 0 := by
            intro α
            rw [hdel α (m + 1) (by omega), ha0s α (m + 1) (by omega)]; ring
          -- `D` and `Dbar` of the adjusted family agree with those of `a0`
          have hDa : ∀ i j : ℕ, ((i : ℂ) + 1)
              * (a0 (i + 1) j + (if i + 1 = 0 ∧ j = 0 then C else 0))
              = (c0 i j - Complex.I * c1 i j) / 2 := by
            intro i j
            rw [hdel (i + 1) j (by omega), add_zero]
            exact hD i j
          have hDbara : ∀ i j : ℕ, ((j : ℂ) + 1)
              * (a0 i (j + 1) + (if i = 0 ∧ j + 1 = 0 then C else 0))
              = (c0 i j + Complex.I * c1 i j) / 2 := by
            intro i j
            rw [hdel i (j + 1) (by omega), add_zero]
            exact hDbar i j
          refine hpin G _ hG ?_ ?_
          · intro j0 z hz
            match j0 with
            | 0 =>
                rw [hc0 z hz, hA _ habd1 habd2 z]
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
                rw [hDa i j, hDbara i j]
                ring
            | 1 =>
                rw [hc1 z hz, hB _ habd1 habd2 z]
                refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
                rw [hDa i j, hDbara i j]
                linear_combination (c1 i j * z ^ i * (starRingEnd ℂ z) ^ j) * hII
          · rw [hPadd a0 (fun i j => if i = 0 ∧ j = 0 then C else 0) z₀,
              hcollapse _ hdel z₀]
            simp only [and_self, if_pos]
            rw [hC]
            ring
  -- ## CONCLUSION: the induction at `d = m` IS the node's statement.
  exact hClaim m le_rfl g hg hvan
