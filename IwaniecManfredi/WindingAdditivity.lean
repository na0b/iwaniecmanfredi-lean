import IwaniecManfredi.WindingCalculus

/-- Two multiplicative properties of the winding number: it is additive under
pointwise products of non-vanishing paths, and the `d`-fold traversal of a
non-vanishing periodic loop multiplies the index by `d`.  The first is what
makes the Rouché step for `A_{n+1} ≠ 0` short; the second is the divisibility
step `ind (χ ∘ ρ_d) = d · ind (χ ∘ ρ_1)`. -/
theorem WindingAdditivity :
    (∀ (α β sg : C(↑unitInterval, ℂ)) (hα : ∀ t, α t ≠ 0) (hβ : ∀ t, β t ≠ 0)
        (hsg : ∀ t, sg t ≠ 0), (∀ t, sg t = α t * β t) →
      WindingNumber sg hsg = WindingNumber α hα + WindingNumber β hβ) ∧
    (∀ ψ : ℝ → ℂ, Continuous ψ → (∀ x, ψ x ≠ 0) → (∀ x, ψ (x + 1) = ψ x) →
      ∀ (d : ℤ) (γ₁ γd : C(↑unitInterval, ℂ)) (h₁ : ∀ t, γ₁ t ≠ 0) (hd : ∀ t, γd t ≠ 0),
        (∀ t : ↑unitInterval, γ₁ t = ψ (t : ℝ)) →
        (∀ t : ↑unitInterval, γd t = ψ ((d : ℝ) * (t : ℝ))) →
        WindingNumber γd hd = (d : ℝ) * WindingNumber γ₁ h₁) := by
  refine ⟨?_, ?_⟩
  -- PART (a): additivity under pointwise products.
  · intro α β sg hα hβ hsg hmul
    obtain ⟨hA, hB, -, -⟩ := WindingCalculus
    obtain ⟨Θα, hα0, hαang, -⟩ := hA α hα
    obtain ⟨Θβ, hβ0, hβang, -⟩ := hA β hβ
    set c : ℝ := Θα 0 + Θβ 0 - Complex.arg (sg 0) with hc
    set Θ : C(↑unitInterval, ℝ) := Θα + Θβ - ContinuousMap.const _ c with hΘ
    have hΘapp : ∀ t, Θ t = Θα t + Θβ t - c := by
      intro t; simp [hΘ]
    -- `↑c = 0` in `Real.Angle`
    have hcang : ((c : ℝ) : Real.Angle) = 0 := by
      have hprod : ((Complex.arg (sg 0) : ℝ) : Real.Angle)
          = ((Complex.arg (α 0) : ℝ) : Real.Angle) + ((Complex.arg (β 0) : ℝ) : Real.Angle) := by
        rw [hmul 0]
        exact Complex.arg_mul_coe_angle (hα 0) (hβ 0)
      rw [hc]
      push_cast [Real.Angle.coe_sub, Real.Angle.coe_add]
      rw [hprod, hα0, hβ0]
      abel
    have hΘ0 : Θ 0 = Complex.arg (sg 0) := by
      rw [hΘapp 0, hc]; ring
    have hΘang : ∀ t, ((Θ t : ℝ) : Real.Angle)
        = ((Complex.arg (sg t) : ℝ) : Real.Angle) := by
      intro t
      have hprod : ((Complex.arg (sg t) : ℝ) : Real.Angle)
          = ((Complex.arg (α t) : ℝ) : Real.Angle) + ((Complex.arg (β t) : ℝ) : Real.Angle) := by
        rw [hmul t]
        exact Complex.arg_mul_coe_angle (hα t) (hβ t)
      rw [hΘapp t, hprod, ← hαang t, ← hβang t]
      push_cast [Real.Angle.coe_sub, Real.Angle.coe_add]
      rw [hcang]
      abel
    -- part (b) of WindingCalculus on all three paths
    have eSG : 2 * Real.pi * WindingNumber sg hsg = Θ 1 - Θ 0 := hB sg hsg Θ hΘ0 hΘang
    have eA : 2 * Real.pi * WindingNumber α hα = Θα 1 - Θα 0 := hB α hα Θα hα0 hαang
    have eB : 2 * Real.pi * WindingNumber β hβ = Θβ 1 - Θβ 0 := hB β hβ Θβ hβ0 hβang
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    refine mul_left_cancel₀ hpi ?_
    rw [eSG, mul_add, eA, eB, hΘapp 1, hΘapp 0]
    ring

  -- PART (b): the d-fold traversal of a 1-periodic non-vanishing loop.
  · intro ψ hψc hψne hψper d γ₁ γd h₁ hd hγ₁ hγd
    obtain ⟨hA, hB, hC, -⟩ := WindingCalculus
    obtain ⟨Θ₁, hΘ₁0, hΘ₁ang, -⟩ := hA γ₁ h₁
    have : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
    have hpi : (2:ℝ) * Real.pi ≠ 0 := by positivity
    -- ψ is invariant under integer translation
    have hψint : ∀ (m : ℤ) (x : ℝ), ψ (x + (m:ℝ)) = ψ x := by
      have hback : ∀ y : ℝ, ψ (y - 1) = ψ y := by
        intro y
        have h := hψper (y - 1)
        rw [sub_add_cancel] at h
        exact h.symm
      intro m
      induction m using Int.induction_on with
      | zero => intro x; simp
      | succ j ih =>
          intro x
          have e : x + (((j:ℤ) + 1 : ℤ) : ℝ) = (x + ((j:ℤ):ℝ)) + 1 := by push_cast; ring
          rw [e, hψper, ih]
      | pred j ih =>
          intro x
          have e : x + ((-(j:ℤ) - 1 : ℤ) : ℝ) = (x - 1) + ((-(j:ℤ) : ℤ) : ℝ) := by push_cast; ring
          rw [e, ih (x - 1), hback]
    -- γ₁ is a loop, so its index is an integer
    have hloop : γ₁ 0 = γ₁ 1 := by
      rw [hγ₁ 0, hγ₁ 1, Set.Icc.coe_zero, Set.Icc.coe_one]
      have h := hψper 0
      rw [zero_add] at h
      exact h.symm
    set δ : ℝ := Θ₁ 1 - Θ₁ 0 with hδdef
    obtain ⟨k, hk⟩ := hC γ₁ h₁ hloop
    have hδ : δ = 2 * Real.pi * (k : ℝ) := by
      have e := hB γ₁ h₁ Θ₁ hΘ₁0 hΘ₁ang
      rw [hk] at e
      rw [hδdef, ← e]
    -- the global branch: a 1-periodic part plus the linear drift δ·x
    set Θe : C(ℝ, ℝ) := ContinuousMap.IccExtend (zero_le_one' ℝ) Θ₁ with hΘe
    have hΘeIcc : ∀ t : ↑unitInterval, Θe (t : ℝ) = Θ₁ t := by
      intro t; rw [hΘe]; simp
    have hΘe0 : Θe (0:ℝ) = Θ₁ 0 := by have h := hΘeIcc 0; simpa using h
    have hΘe1 : Θe (1:ℝ) = Θ₁ 1 := by have h := hΘeIcc 1; simpa using h
    set g : ℝ → ℝ := fun x => Θe x - δ * x with hgdef
    have hgcont : Continuous g := by
      rw [hgdef]; exact Θe.continuous.sub (continuous_const.mul continuous_id)
    have hgend : g 0 = g (0 + 1) := by
      rw [hgdef]
      simp only [zero_add, hΘe0, hΘe1, mul_zero, mul_one, sub_zero, hδdef]
      ring
    set Ψ : ℝ → ℝ := fun x => AddCircle.liftIco (1:ℝ) 0 g ((x : AddCircle (1:ℝ))) with hΨdef
    have hΨcont : Continuous Ψ := by
      rw [hΨdef]
      exact (AddCircle.liftIco_continuous hgend hgcont.continuousOn).comp continuous_quotient_mk'
    have hΨper : ∀ x : ℝ, Ψ (x + 1) = Ψ x := by
      intro x
      rw [hΨdef]; simp only; congr 1
      exact AddCircle.coe_add_period 1 x
    have hΨIco : ∀ x : ℝ, x ∈ Set.Ico (0:ℝ) 1 → Ψ x = g x := by
      intro x hx
      rw [hΨdef]; simp only
      exact AddCircle.liftIco_coe_apply (by rwa [zero_add])
    set Φ : ℝ → ℝ := fun x => Ψ x + δ * x with hΦdef
    have hΦcont : Continuous Φ := by
      rw [hΦdef]; exact hΨcont.add (continuous_const.mul continuous_id)
    have hΦIco : ∀ x : ℝ, x ∈ Set.Ico (0:ℝ) 1 → Φ x = Θe x := by
      intro x hx
      rw [hΦdef]; simp only [hΨIco x hx, hgdef]; ring
    have hΦper : ∀ x : ℝ, Φ (x + 1) = Φ x + δ := by
      intro x; rw [hΦdef]; simp only [hΨper x]; ring
    have hΦint : ∀ (m : ℤ) (x : ℝ), Φ (x + (m:ℝ)) = Φ x + (m:ℝ) * δ := by
      have hback : ∀ y : ℝ, Φ (y - 1) = Φ y - δ := by
        intro y
        have h := hΦper (y - 1)
        rw [sub_add_cancel] at h
        linarith [h]
      intro m
      induction m using Int.induction_on with
      | zero => intro x; simp
      | succ j ih =>
          intro x
          have e : x + (((j:ℤ) + 1 : ℤ) : ℝ) = (x + ((j:ℤ):ℝ)) + 1 := by push_cast; ring
          rw [e, hΦper, ih]
          push_cast; ring
      | pred j ih =>
          intro x
          have e : x + ((-(j:ℤ) - 1 : ℤ) : ℝ) = (x - 1) + ((-(j:ℤ) : ℤ) : ℝ) := by push_cast; ring
          rw [e, ih (x - 1), hback]
          push_cast; ring
    have hΦ0 : Φ 0 = Θ₁ 0 := by rw [hΦIco 0 ⟨le_refl 0, one_pos⟩, hΘe0]
    -- Φ is a branch of the argument of ψ on all of ℝ
    have hΦang : ∀ x : ℝ, ((Φ x : ℝ) : Real.Angle) = ((Complex.arg (ψ x) : ℝ) : Real.Angle) := by
      intro x
      have hfr : Int.fract x ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
      have hxe : x = Int.fract x + ((⌊x⌋ : ℤ) : ℝ) := (Int.fract_add_floor x).symm
      have hmem : Int.fract x ∈ unitInterval := ⟨hfr.1, le_of_lt hfr.2⟩
      have h1 : ((Φ (Int.fract x) : ℝ) : Real.Angle)
          = ((Complex.arg (ψ (Int.fract x)) : ℝ) : Real.Angle) := by
        rw [hΦIco _ hfr, hΘeIcc ⟨Int.fract x, hmem⟩, hΘ₁ang ⟨Int.fract x, hmem⟩,
          hγ₁ ⟨Int.fract x, hmem⟩]
      have h3 : ((((⌊x⌋ : ℤ) : ℝ) * δ : ℝ) : Real.Angle) = 0 := by
        rw [← Real.Angle.coe_zero]
        refine Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨⌊x⌋ * k, ?_⟩
        rw [sub_zero, hδ]; push_cast; ring
      have hψx : ψ x = ψ (Int.fract x) := by
        have h := hψint ⌊x⌋ (Int.fract x)
        rw [← hxe] at h
        exact h
      have hΦx : Φ x = Φ (Int.fract x) + ((⌊x⌋ : ℤ) : ℝ) * δ := by
        have h := hΦint ⌊x⌋ (Int.fract x)
        rw [← hxe] at h
        exact h
      calc ((Φ x : ℝ) : Real.Angle)
          = ((Φ (Int.fract x) + ((⌊x⌋ : ℤ) : ℝ) * δ : ℝ) : Real.Angle) := by rw [hΦx]
        _ = ((Φ (Int.fract x) : ℝ) : Real.Angle) + ((((⌊x⌋ : ℤ) : ℝ) * δ : ℝ) : Real.Angle) := by
            rw [Real.Angle.coe_add]
        _ = ((Complex.arg (ψ (Int.fract x)) : ℝ) : Real.Angle) := by rw [h1, h3, add_zero]
        _ = ((Complex.arg (ψ x) : ℝ) : Real.Angle) := by rw [hψx]
    -- the branch for γd
    set Θd : C(↑unitInterval, ℝ) :=
      ⟨fun t => Φ ((d:ℝ) * (t:ℝ)),
        hΦcont.comp (continuous_const.mul continuous_subtype_val)⟩ with hΘddef
    have hΘdapp : ∀ t : ↑unitInterval, Θd t = Φ ((d:ℝ) * (t:ℝ)) := by
      intro t; rw [hΘddef]; rfl
    have hΘd0 : Θd 0 = Complex.arg (γd 0) := by
      rw [hΘdapp 0, hγd 0, Set.Icc.coe_zero, mul_zero, hΦ0, hΘ₁0, hγ₁ 0, Set.Icc.coe_zero]
    have hΘdang : ∀ t : ↑unitInterval, ((Θd t : ℝ) : Real.Angle)
        = ((Complex.arg (γd t) : ℝ) : Real.Angle) := by
      intro t
      rw [hΘdapp t, hΦang ((d:ℝ) * (t:ℝ)), hγd t]
    -- conclude
    have ed := hB γd hd Θd hΘd0 hΘdang
    have e1 := hB γ₁ h₁ Θ₁ hΘ₁0 hΘ₁ang
    have e1' : 2 * Real.pi * WindingNumber γ₁ h₁ = δ := by rw [e1, hδdef]
    have hdd : Φ ((d:ℝ)) = Φ 0 + (d:ℝ) * δ := by
      have h := hΦint d 0
      rw [zero_add] at h
      exact h
    refine mul_left_cancel₀ hpi ?_
    rw [ed, hΘdapp 1, hΘdapp 0, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, hdd]
    have : 2 * Real.pi * ((d:ℝ) * WindingNumber γ₁ h₁)
        = (d:ℝ) * (2 * Real.pi * WindingNumber γ₁ h₁) := by ring
    rw [this, e1']
    ring
