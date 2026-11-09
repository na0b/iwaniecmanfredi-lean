import IwaniecManfredi.WindingNumber

/-- Homotopy invariance of the winding number.  The homotopy is carried by maps
into the subtype `{z : ℂ // z ≠ 0}`, so "through `ℂ - {0}`" is structural rather
than a side condition, and the two paths are pinned to those maps. -/
theorem WindingHomotopyInvariance (γ₀ γ₁ : C(↑unitInterval, ℂ))
    (hne₀ : ∀ t, γ₀ t ≠ 0) (hne₁ : ∀ t, γ₁ t ≠ 0)
    (g₀ g₁ : C(↑unitInterval, {z : ℂ // z ≠ 0}))
    (hg₀ : ∀ t, ((g₀ t : ℂ)) = γ₀ t) (hg₁ : ∀ t, ((g₁ t : ℂ)) = γ₁ t)
    (hh : g₀.HomotopicRel g₁ {0, 1}) :
    WindingNumber γ₀ hne₀ = WindingNumber γ₁ hne₁ := by
  have hA : Continuous
      (fun w : {z : ℂ // z ≠ 0} => ((Complex.arg (w : ℂ) : ℝ) : Real.Angle)) := by
    refine continuous_iff_continuousAt.2 fun w => ?_
    exact (Complex.continuousAt_arg_coe_angle w.2).comp
      continuous_subtype_val.continuousAt
  set A : C({z : ℂ // z ≠ 0}, Real.Angle) := ⟨_, hA⟩ with hAdef
  have hb : γ₀ 0 = γ₁ 0 := by
    have h := hh.fst_eq_snd (show (0 : ↑unitInterval) ∈ ({0, 1} : Set ↑unitInterval) from
      Or.inl rfl)
    rw [← hg₀ 0, ← hg₁ 0, h]
  have harg : Complex.arg (γ₀ 0) = Complex.arg (γ₁ 0) := by rw [hb]
  -- the two Angle paths, as mk's with explicit continuity proofs
  have hc₀ : Continuous (fun t : ↑unitInterval => ((Complex.arg (γ₀ t) : ℝ) : Real.Angle)) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Complex.continuousAt_arg_coe_angle (hne₀ t)).comp γ₀.continuous.continuousAt
  have hc₁ : Continuous (fun t : ↑unitInterval => ((Complex.arg (γ₁ t) : ℝ) : Real.Angle)) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Complex.continuousAt_arg_coe_angle (hne₁ t)).comp γ₁.continuous.continuousAt
  have e₀ : A.comp g₀ = (⟨_, hc₀⟩ : C(↑unitInterval, Real.Angle)) := by
    ext t; simp [hAdef, hg₀ t]
  have e₁ : A.comp g₁ = (⟨_, hc₁⟩ : C(↑unitInterval, Real.Angle)) := by
    ext t; simp [hAdef, hg₁ t]
  have hhom : (⟨_, hc₀⟩ : C(↑unitInterval, Real.Angle)).HomotopicRel ⟨_, hc₁⟩ {0, 1} := by
    rw [← e₀, ← e₁]; exact hh.comp_continuousMap A
  simp only [WindingNumber, harg]
  congr 2
  refine (AddCircle.isCoveringMap_coe (2 * Real.pi)).liftPath_apply_one_eq_of_homotopicRel
    hhom _ ?_ ?_
