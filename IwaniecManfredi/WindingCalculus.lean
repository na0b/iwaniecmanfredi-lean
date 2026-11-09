import IwaniecManfredi.WindingNumber

/-- The basic calculus of the winding number: (a) existence of a continuous
real branch of the argument along a non-vanishing path, normalised at `t = 0`,
with the polar representation it provides; (b) the characterisation of the
index as the increment of any such branch; (c) integrality for loops; and
(d) the value `k` on the model circle `t ↦ w e^{2πikt}`. -/
theorem WindingCalculus :
    (∀ (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0),
      ∃ Θ : C(↑unitInterval, ℝ),
        Θ 0 = Complex.arg (γ 0) ∧
        (∀ t, ((Θ t : ℝ) : Real.Angle) = ((Complex.arg (γ t) : ℝ) : Real.Angle)) ∧
        (∀ t, γ t = ((‖γ t‖ : ℝ) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) ∧
    (∀ (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0) (Θ : C(↑unitInterval, ℝ)),
      Θ 0 = Complex.arg (γ 0) →
      (∀ t, ((Θ t : ℝ) : Real.Angle) = ((Complex.arg (γ t) : ℝ) : Real.Angle)) →
      2 * Real.pi * WindingNumber γ hne = Θ 1 - Θ 0) ∧
    (∀ (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0), γ 0 = γ 1 →
      ∃ k : ℤ, WindingNumber γ hne = (k : ℝ)) ∧
    (∀ (w : ℂ) (k : ℤ) (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0), w ≠ 0 →
      (∀ t : ↑unitInterval,
        γ t = w * Complex.exp (2 * Real.pi * (k : ℝ) * (t : ℝ) * Complex.I)) →
      WindingNumber γ hne = (k : ℝ)) := by
  have arg_polar_coe_angle : ∀ r θ : ℝ, 0 < r →
      ((Complex.arg ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) : ℝ) : Real.Angle)
        = ((θ : ℝ) : Real.Angle) := by
    intro r θ hr
    have hexp : Complex.exp ((θ : ℂ) * Complex.I)
        = (Real.Angle.cos ((θ : ℝ) : Real.Angle) : ℂ)
          + (Real.Angle.sin ((θ : ℝ) : Real.Angle) : ℂ) * Complex.I := by
      rw [Real.Angle.cos_coe, Real.Angle.sin_coe, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hexp]
    exact Complex.arg_mul_cos_add_sin_mul_I_coe_angle hr _
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hcont : ∀ (γ : C(↑unitInterval, ℂ)), (∀ t, γ t ≠ 0) →
      Continuous (fun t : ↑unitInterval => ((Complex.arg (γ t) : ℝ) : Real.Angle)) := by
    intro γ hne
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Complex.continuousAt_arg_coe_angle (hne t)).comp γ.continuous.continuousAt
  -- (b): ANY continuous branch of the argument computes the index.
  -- This is uniqueness of path lifts, `IsCoveringMap.eq_liftPath_iff'`.
  have hB : ∀ (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0) (Θ : C(↑unitInterval, ℝ)),
      Θ 0 = Complex.arg (γ 0) →
      (∀ t, ((Θ t : ℝ) : Real.Angle) = ((Complex.arg (γ t) : ℝ) : Real.Angle)) →
      2 * Real.pi * WindingNumber γ hne = Θ 1 - Θ 0 := by
    intro γ hne Θ h0 hcg
    have heq : Θ = (AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
        ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl :=
      ((AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_liftPath_iff' rfl).2
        ⟨funext fun t => hcg t, h0⟩
    have hdef : WindingNumber γ hne = (Θ 1 - Complex.arg (γ 0)) / (2 * Real.pi) := by
      rw [heq]; rfl
    rw [hdef, ← h0, mul_div_cancel₀ _ hpi]
  -- (a): the lift IS a branch.
  have hA : ∀ (γ : C(↑unitInterval, ℂ)) (hne : ∀ t, γ t ≠ 0),
      ∃ Θ : C(↑unitInterval, ℝ),
        Θ 0 = Complex.arg (γ 0) ∧
        (∀ t, ((Θ t : ℝ) : Real.Angle) = ((Complex.arg (γ t) : ℝ) : Real.Angle)) ∧
        (∀ t, γ t = ((‖γ t‖ : ℝ) : ℂ)
          * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
    intro γ hne
    refine ⟨(AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
      ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl, ?_, ?_, ?_⟩
    · exact (AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath_zero _ _ _
    · intro t
      exact congrFun ((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath_lifts
        ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl) t
    · intro t
      have hang : ((((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
            ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl t : ℝ)) : Real.Angle)
          = ((Complex.arg (γ t) : ℝ) : Real.Angle) :=
        congrFun ((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath_lifts
          ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl) t
      obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
      have hexp : Complex.exp (((((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
            ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl t : ℝ)) : ℂ) * Complex.I)
          = Complex.exp (((Complex.arg (γ t) : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨m, ?_⟩
        have hre : (((AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath
            ⟨_, hcont γ hne⟩ (Complex.arg (γ 0)) rfl t : ℝ))
            = Complex.arg (γ t) + 2 * Real.pi * (m : ℝ) := by linarith [hm]
        rw [hre]; push_cast; ring
      rw [hexp, Complex.norm_mul_exp_arg_mul_I]
  refine ⟨hA, hB, ?_, ?_⟩
  · -- (c): integrality for loops
    intro γ hne hloop
    obtain ⟨Θ, h0, hcg, -⟩ := hA γ hne
    have hend : ((Θ 1 : ℝ) : Real.Angle) = ((Θ 0 : ℝ) : Real.Angle) := by
      rw [hcg 1, hcg 0]
      exact congrArg _ (congrArg Complex.arg hloop.symm)
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hend
    refine ⟨m, mul_left_cancel₀ hpi ?_⟩
    rw [hB γ hne Θ h0 hcg, hm]
  · -- (d): the model circle has index k
    intro w k γ hne hw hγ
    have hΘc : Continuous (fun t : ↑unitInterval =>
        Complex.arg w + 2 * Real.pi * (k : ℝ) * (t : ℝ)) := by
      fun_prop
    set Θ : C(↑unitInterval, ℝ) := ⟨_, hΘc⟩ with hΘ
    have hw0 : (0 : ℝ) < ‖w‖ := by simpa using hw
    have h0 : Θ 0 = Complex.arg (γ 0) := by
      have hg0 : γ 0 = w := by rw [hγ 0]; norm_num
      rw [hg0, hΘ]; simp
    have hcg : ∀ t, ((Θ t : ℝ) : Real.Angle) = ((Complex.arg (γ t) : ℝ) : Real.Angle) := by
      intro t
      have hsplit : ((Complex.arg w + 2 * Real.pi * (k : ℝ) * ((t : ℝ)) : ℝ) : ℂ) * Complex.I
          = ((Complex.arg w : ℝ) : ℂ) * Complex.I
            + 2 * ((Real.pi : ℝ) : ℂ) * (((k : ℝ)) : ℂ) * (((t : ℝ)) : ℂ) * Complex.I := by
        push_cast; ring
      have hgt : γ t = ((‖w‖ : ℝ) : ℂ)
          * Complex.exp (((Complex.arg w + 2 * Real.pi * (k : ℝ) * ((t : ℝ)) : ℝ) : ℂ)
            * Complex.I) := by
        rw [hγ t, hsplit, Complex.exp_add, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
      rw [hgt, arg_polar_coe_angle _ _ hw0]
      rfl
    refine mul_left_cancel₀ hpi ?_
    rw [hB γ hne Θ h0 hcg, hΘ]
    simp
