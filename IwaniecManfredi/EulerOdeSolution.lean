import IwaniecManfredi.LambdaCoef
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-- The general solution of the Euler equation (35) on `(0,1)`:
`y = A⁺ r^{λ⁺} + A⁻ r^{λ⁻}` with `λ⁺ = λ_{|k|}(n,p)` and `λ⁻ = -pn - λ⁺` the
two roots of the indicial equation.  The substitution `r = e^t` turns `r d/dr`
into `d/dt`, so no ODE machinery is needed: two integrating-factor steps and the
fact that a function with vanishing derivative on an interval is constant.  The
hypothesis `k ≠ 0 ∨ p ≠ 2` is exactly the positivity of the indicial
discriminant `4k²(p-1) + n²(p-2)²`, which is what makes the paper's claim at
line 313 that the two roots are distinct correct; it fails only at `k = 0`,
`p = 2`, where the roots coincide and a logarithm enters. -/
theorem EulerOdeSolution (n : ℕ) (p : ℝ) (k : ℤ) (hn : 1 ≤ n) (hp : 1 < p)
    (hdeg : k ≠ 0 ∨ p ≠ 2)
    (y : ℝ → ℂ) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioo (0 : ℝ) 1))
    (hode : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ((r : ℝ) : ℂ) * deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s) r
        + ((p * (n : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) * deriv y r
        + ((((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) : ℝ) : ℂ) * y r = 0) :
    ∃ Ap Am : ℂ, ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      y r = Ap * ((r ^ LambdaCoef n k.natAbs p : ℝ) : ℂ)
        + Am * ((r ^ (-(p * (n : ℝ)) - LambdaCoef n k.natAbs p) : ℝ) : ℂ) := by
  have hIo : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hIp : IsPreconnected (Set.Ioo (0 : ℝ) 1) := (convex_Ioo (0 : ℝ) 1).isPreconnected
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- All the `Real.rpow` bookkeeping, done once up front.
  have hmulrpow : ∀ r : ℝ, 0 < r → ∀ x z w : ℝ, x + z = w →
      ((r ^ x : ℝ) : ℂ) * ((r ^ z : ℝ) : ℂ) = ((r ^ w : ℝ) : ℂ) := by
    intro r hr x z w hxz
    rw [← Complex.ofReal_mul, ← Real.rpow_add hr, hxz]
  have hmulr : ∀ r : ℝ, 0 < r → ∀ x w : ℝ, x + 1 = w →
      ((r ^ x : ℝ) : ℂ) * ((r : ℝ) : ℂ) = ((r ^ w : ℝ) : ℂ) := by
    intro r hr x w hxw
    rw [show ((r : ℝ) : ℂ) = ((r ^ (1 : ℝ) : ℝ) : ℂ) from by rw [Real.rpow_one]]
    exact hmulrpow r hr x 1 w hxw
  have hinvrpow : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      ((r ^ (-x) : ℝ) : ℂ) * ((r ^ x : ℝ) : ℂ) = 1 := by
    intro r hr x
    rw [hmulrpow r hr (-x) x 0 (by ring), Real.rpow_zero, Complex.ofReal_one]
  -- The two indicial roots.
  set L := LambdaCoef n k.natAbs p with hLdef
  set M := -(p * (n : ℝ)) - L with hMdef
  have hkabs : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by simp [sq_abs]
  -- `hdeg` is exactly positivity of the indicial discriminant.
  have hD0 : (0 : ℝ) < 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
    rcases hdeg with hk | hpp
    · have hk0 : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
      have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := sq_pos_of_ne_zero hk0
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (p - 2) ^ 2 := by positivity
      nlinarith
    · have hpp0 : p - 2 ≠ 0 := fun h => hpp (by linarith)
      have hp2 : (0 : ℝ) < (p - 2) ^ 2 := sq_pos_of_ne_zero hpp0
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
      have hnn : (0 : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (p - 1) := by positivity
      nlinarith
  have hL2 : 2 * L
      = -((n : ℝ) * p)
        + Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) := by
    rw [hLdef]
    unfold LambdaCoef
    rw [hkabs]
    ring
  have hS2 : (2 * L + (n : ℝ) * p) ^ 2
      = 4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2 := by
    rw [show 2 * L + (n : ℝ) * p
        = Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) from by
          linear_combination hL2]
    exact Real.sq_sqrt hD0.le
  -- The root identity, and the two symmetric functions of the roots.
  have hroot : L ^ 2 + p * (n : ℝ) * L + ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) = 0 := by
    linear_combination hS2 / 4
  have hLMsum : L + M = -(p * (n : ℝ)) := by rw [hMdef]; ring
  have hLMprod : L * M = ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1) := by
    rw [hMdef]; linear_combination -hroot
  have hLMpos : 0 < L - M := by
    have hs : 0 < Real.sqrt (4 * (k : ℝ) ^ 2 * (p - 1) + (n : ℝ) ^ 2 * (p - 2) ^ 2) :=
      Real.sqrt_pos.mpr hD0
    rw [hMdef]
    linarith [hL2]
  have hMLne : ((M : ℝ) : ℂ) - ((L : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h
    linarith
  have hLMsumC : ((L : ℝ) : ℂ) + ((M : ℝ) : ℂ) = -(((p * (n : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, hLMsum, Complex.ofReal_neg]
  have hLMprodC : ((L : ℝ) : ℂ) * ((M : ℝ) : ℂ)
      = (((((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * (p - 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hLMprod]
  -- Differentiability of `y` and `deriv y` on the open interval.
  obtain ⟨hyd, hy1⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hIo).mp hy
  obtain ⟨hy1d, -⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hIo).mp hy1
  have hyA : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt y (deriv y r) r := fun r hr =>
    (hyd.differentiableAt (hIo.mem_nhds hr)).hasDerivAt
  have hy1A : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (deriv y) (deriv (deriv y) r) r := fun r hr =>
    (hy1d.differentiableAt (hIo.mem_nhds hr)).hasDerivAt
  have hP : ∀ r : ℝ, HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 r := fun r => by
    simpa using (hasDerivAt_id r).ofReal_comp
  -- The equation in the normalised form `r² y'' + (1 - L - M) r y' + L M y = 0`.
  have hodeN : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ((r : ℝ) : ℂ) ^ 2 * deriv (deriv y) r
        + (1 - ((L : ℝ) : ℂ) - ((M : ℝ) : ℂ)) * ((r : ℝ) : ℂ) * deriv y r
        + ((L : ℝ) : ℂ) * ((M : ℝ) : ℂ) * y r = 0 := by
    intro r hr
    have hd1 : DifferentiableAt ℝ (fun s : ℝ => ((s : ℝ) : ℂ)) r := (hP r).differentiableAt
    have hd2 : DifferentiableAt ℝ (deriv y) r := (hy1A r hr).differentiableAt
    have hmul : deriv (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s) r
        = deriv (fun s : ℝ => ((s : ℝ) : ℂ)) r * deriv y r
          + ((r : ℝ) : ℂ) * deriv (deriv y) r := deriv_fun_mul hd1 hd2
    have hone : deriv (fun s : ℝ => ((s : ℝ) : ℂ)) r = 1 := (hP r).deriv
    have h := hode r hr
    rw [hmul, hone] at h
    linear_combination h - (((r : ℝ) : ℂ) * deriv y r) * hLMsumC + (y r) * hLMprodC
  -- FIRST INTEGRATING FACTOR: `G r = r^(-M) * (r y' - L y)` has zero derivative.
  have hGd : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => ((s ^ (-M) : ℝ) : ℂ) * (((s : ℝ) : ℂ) * deriv y s - ((L : ℝ) : ℂ) * y s))
        0 r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hA : HasDerivAt (fun s : ℝ => ((s ^ (-M) : ℝ) : ℂ))
        (((-M) * r ^ (-M - 1) : ℝ) : ℂ) r :=
      (Real.hasDerivAt_rpow_const (Or.inl hrne)).ofReal_comp
    have hB : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) * deriv y s - ((L : ℝ) : ℂ) * y s)
        (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r - ((L : ℝ) : ℂ) * deriv y r) r :=
      ((hP r).fun_mul (hy1A r hr)).sub ((hyA r hr).const_mul ((L : ℝ) : ℂ))
    have hG : HasDerivAt
        (fun s : ℝ => ((s ^ (-M) : ℝ) : ℂ) * (((s : ℝ) : ℂ) * deriv y s - ((L : ℝ) : ℂ) * y s))
        ((((-M) * r ^ (-M - 1) : ℝ) : ℂ)
            * (((r : ℝ) : ℂ) * deriv y r - ((L : ℝ) : ℂ) * y r)
          + ((r ^ (-M) : ℝ) : ℂ)
            * (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r - ((L : ℝ) : ℂ) * deriv y r))
        r := hA.fun_mul hB
    have hz : (((-M) * r ^ (-M - 1) : ℝ) : ℂ)
          * (((r : ℝ) : ℂ) * deriv y r - ((L : ℝ) : ℂ) * y r)
        + ((r ^ (-M) : ℝ) : ℂ)
          * (1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r - ((L : ℝ) : ℂ) * deriv y r)
        = 0 := by
      have h := hodeN r hr
      have hstep : ((r ^ (-M - 1) : ℝ) : ℂ) * ((r : ℝ) : ℂ) = ((r ^ (-M) : ℝ) : ℂ) :=
        hmulr r hr0 (-M - 1) (-M) (by ring)
      push_cast
      linear_combination
        (-(1 * deriv y r + ((r : ℝ) : ℂ) * deriv (deriv y) r - ((L : ℝ) : ℂ) * deriv y r))
            * hstep
          + ((r ^ (-M - 1) : ℝ) : ℂ) * h
    rw [← hz]
    exact hG
  obtain ⟨Cc, hCc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIp
    (fun r hr => ((hGd r hr).differentiableAt).differentiableWithinAt)
    (fun r hr => by simpa using (hGd r hr).deriv)
  -- `r y' - L y = Cc r^M`.
  have hW2 : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      ((r : ℝ) : ℂ) * deriv y r - ((L : ℝ) : ℂ) * y r = Cc * ((r ^ M : ℝ) : ℂ) := by
    intro r hr
    have h := hCc r hr
    have hone : ((r ^ (-M) : ℝ) : ℂ) * ((r ^ M : ℝ) : ℂ) = 1 := hinvrpow r hr.1 M
    linear_combination ((r ^ M : ℝ) : ℂ) * h
      - (((r : ℝ) : ℂ) * deriv y r - ((L : ℝ) : ℂ) * y r) * hone
  -- SECOND INTEGRATING FACTOR, where `L ≠ M` is spent.
  have hAm : Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) * (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) = Cc :=
    div_mul_cancel₀ Cc hMLne
  have hFd : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => ((s ^ (-L) : ℝ) : ℂ) * y s
          - Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) * ((s ^ (M - L) : ℝ) : ℂ)) 0 r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hA : HasDerivAt (fun s : ℝ => ((s ^ (-L) : ℝ) : ℂ))
        (((-L) * r ^ (-L - 1) : ℝ) : ℂ) r :=
      (Real.hasDerivAt_rpow_const (Or.inl hrne)).ofReal_comp
    have hC : HasDerivAt (fun s : ℝ => Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ))
          * ((s ^ (M - L) : ℝ) : ℂ))
        (Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) * (((M - L) * r ^ (M - L - 1) : ℝ) : ℂ)) r :=
      ((Real.hasDerivAt_rpow_const (Or.inl hrne)).ofReal_comp).const_mul _
    have hF : HasDerivAt
        (fun s : ℝ => ((s ^ (-L) : ℝ) : ℂ) * y s
          - Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) * ((s ^ (M - L) : ℝ) : ℂ))
        ((((-L) * r ^ (-L - 1) : ℝ) : ℂ) * y r + ((r ^ (-L) : ℝ) : ℂ) * deriv y r
          - Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ))
              * (((M - L) * r ^ (M - L - 1) : ℝ) : ℂ)) r := (hA.fun_mul (hyA r hr)).sub hC
    have hz : (((-L) * r ^ (-L - 1) : ℝ) : ℂ) * y r + ((r ^ (-L) : ℝ) : ℂ) * deriv y r
          - Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)) * (((M - L) * r ^ (M - L - 1) : ℝ) : ℂ)
        = 0 := by
      have h := hW2 r hr
      have ha : ((r ^ (-L - 1) : ℝ) : ℂ) * ((r : ℝ) : ℂ) = ((r ^ (-L) : ℝ) : ℂ) :=
        hmulr r hr0 (-L - 1) (-L) (by ring)
      have hb : ((r ^ (-L - 1) : ℝ) : ℂ) * ((r ^ M : ℝ) : ℂ) = ((r ^ (M - L - 1) : ℝ) : ℂ) :=
        hmulrpow r hr0 (-L - 1) M (M - L - 1) (by ring)
      push_cast
      linear_combination (-(deriv y r)) * ha + Cc * hb
        + ((r ^ (-L - 1) : ℝ) : ℂ) * h
        + (-(((r ^ (M - L - 1) : ℝ) : ℂ))) * hAm
    rw [← hz]
    exact hF
  obtain ⟨Ap, hAp⟩ := hIo.exists_is_const_of_deriv_eq_zero hIp
    (fun r hr => ((hFd r hr).differentiableAt).differentiableWithinAt)
    (fun r hr => by simpa using (hFd r hr).deriv)
  -- Multiply back by `r^L`.
  refine ⟨Ap, Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ)), ?_⟩
  intro r hr
  have h := hAp r hr
  have hq1 : ((r ^ (-L) : ℝ) : ℂ) * ((r ^ L : ℝ) : ℂ) = 1 := hinvrpow r hr.1 L
  have hq2 : ((r ^ (M - L) : ℝ) : ℂ) * ((r ^ L : ℝ) : ℂ) = ((r ^ M : ℝ) : ℂ) :=
    hmulrpow r hr.1 (M - L) L M (by ring)
  linear_combination ((r ^ L : ℝ) : ℂ) * h - (y r) * hq1
    + (Cc / (((M : ℝ) : ℂ) - ((L : ℝ) : ℂ))) * hq2
