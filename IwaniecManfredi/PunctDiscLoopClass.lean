import IwaniecManfredi.WindingCalculus

/-- Classification of loops in a punctured disc by their index: two loops in
`{0 < ‖z‖ < δ}` with the same basepoint and the same winding number are
homotopic relative to `{0,1}` inside that punctured disc.  The homotopy is
explicit -- interpolate modulus and lifted argument linearly -- and the
equality of the indices is used exactly once, to make the lifted arguments
agree at `t = 1`. -/
theorem PunctDiscLoopClass (δ : ℝ) (hδ : 0 < δ) (γ₀ γ₁ : C(↑unitInterval, ℂ))
    (hne₀ : ∀ t, γ₀ t ≠ 0) (hne₁ : ∀ t, γ₁ t ≠ 0)
    (hb₀ : ∀ t, ‖γ₀ t‖ < δ) (hb₁ : ∀ t, ‖γ₁ t‖ < δ)
    (hloop₀ : γ₀ 0 = γ₀ 1) (hloop₁ : γ₁ 0 = γ₁ 1) (hbase : γ₀ 0 = γ₁ 0)
    (hind : WindingNumber γ₀ hne₀ = WindingNumber γ₁ hne₁) :
    ∃ g₀ g₁ : C(↑unitInterval, {z : ℂ // z ≠ 0 ∧ ‖z‖ < δ}),
      (∀ t, ((g₀ t : ℂ)) = γ₀ t) ∧ (∀ t, ((g₁ t : ℂ)) = γ₁ t) ∧
        g₀.HomotopicRel g₁ {0, 1} := by
  obtain ⟨hA, hB, -, -⟩ := WindingCalculus
  obtain ⟨Θ₀, hΘ₀0, hΘ₀arg, hΘ₀pol⟩ := hA γ₀ hne₀
  obtain ⟨Θ₁, hΘ₁0, hΘ₁arg, hΘ₁pol⟩ := hA γ₁ hne₁
  -- the two branches agree at t = 0 (same basepoint) and at t = 1 (same index)
  have hΘ0 : Θ₀ 0 = Θ₁ 0 := by rw [hΘ₀0, hΘ₁0, hbase]
  have hΘ1 : Θ₀ 1 = Θ₁ 1 := by
    have e₀ := hB γ₀ hne₀ Θ₀ hΘ₀0 hΘ₀arg
    have e₁ := hB γ₁ hne₁ Θ₁ hΘ₁0 hΘ₁arg
    rw [hind] at e₀
    rw [← hΘ0] at e₁
    linarith [e₀, e₁]
  -- modulus bounds for the linear interpolation of the two moduli
  have hcpos : ∀ (s t : ↑unitInterval),
      0 < (1 - (s:ℝ)) * ‖γ₀ t‖ + (s:ℝ) * ‖γ₁ t‖ := by
    intro s t
    have hs0 : (0:ℝ) ≤ (s:ℝ) := s.2.1
    have hs1 : (s:ℝ) ≤ 1 := s.2.2
    have hA0 : 0 < ‖γ₀ t‖ := norm_pos_iff.mpr (hne₀ t)
    have hB0 : 0 < ‖γ₁ t‖ := norm_pos_iff.mpr (hne₁ t)
    rcases eq_or_lt_of_le hs1 with h | h
    · rw [h]; simpa using hB0
    · have h1 : 0 < 1 - (s:ℝ) := by linarith
      nlinarith [mul_pos h1 hA0, mul_nonneg hs0 hB0.le]
  have hclt : ∀ (s t : ↑unitInterval),
      (1 - (s:ℝ)) * ‖γ₀ t‖ + (s:ℝ) * ‖γ₁ t‖ < δ := by
    intro s t
    have hs0 : (0:ℝ) ≤ (s:ℝ) := s.2.1
    have hs1 : (s:ℝ) ≤ 1 := s.2.2
    have h0 := hb₀ t
    have h1 := hb₁ t
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr h1.le),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (s:ℝ)) (sub_nonneg.mpr h0.le)]
  -- the ℂ-valued homotopy
  set Fc : ↑unitInterval × ↑unitInterval → ℂ := fun st =>
    ((((1 - (st.1:ℝ)) * ‖γ₀ st.2‖ + (st.1:ℝ) * ‖γ₁ st.2‖ : ℝ)) : ℂ) *
      Complex.exp ((((1 - (st.1:ℝ)) * Θ₀ st.2 + (st.1:ℝ) * Θ₁ st.2 : ℝ) : ℂ) * Complex.I)
    with hFc
  have hFcnorm : ∀ st : ↑unitInterval × ↑unitInterval,
      ‖Fc st‖ = (1 - (st.1:ℝ)) * ‖γ₀ st.2‖ + (st.1:ℝ) * ‖γ₁ st.2‖ := by
    intro st
    rw [hFc]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_pos (hcpos st.1 st.2)
  have hFcmem : ∀ st : ↑unitInterval × ↑unitInterval, Fc st ≠ 0 ∧ ‖Fc st‖ < δ := by
    intro st
    refine ⟨?_, ?_⟩
    · rw [← norm_ne_zero_iff, hFcnorm]; exact ne_of_gt (hcpos st.1 st.2)
    · rw [hFcnorm]; exact hclt st.1 st.2
  have hFccont : Continuous Fc := by
    rw [hFc]
    fun_prop
  -- endpoints in s
  have hF0 : ∀ t : ↑unitInterval, Fc (0, t) = γ₀ t := by
    intro t
    rw [hFc]
    simp only [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact (hΘ₀pol t).symm
  have hF1 : ∀ t : ↑unitInterval, Fc (1, t) = γ₁ t := by
    intro t
    rw [hFc]
    simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    exact (hΘ₁pol t).symm
  -- rel {0,1}
  have hγ1eq : γ₀ 1 = γ₁ 1 := by rw [← hloop₀, hbase, hloop₁]
  have hFrel : ∀ (s : ↑unitInterval) (x : ↑unitInterval), x = 0 ∨ x = 1 → Fc (s, x) = γ₀ x := by
    intro s x hx
    have hs0 : (0:ℝ) ≤ (s:ℝ) := s.2.1
    rcases hx with rfl | rfl
    · rw [hFc]
      simp only
      rw [← hbase, ← hΘ0]
      have hn : (1 - (s:ℝ)) * ‖γ₀ (0 : ↑unitInterval)‖ + (s:ℝ) * ‖γ₀ (0 : ↑unitInterval)‖
          = ‖γ₀ (0 : ↑unitInterval)‖ := by ring
      have he : (1 - (s:ℝ)) * Θ₀ (0 : ↑unitInterval) + (s:ℝ) * Θ₀ (0 : ↑unitInterval)
          = Θ₀ (0 : ↑unitInterval) := by ring
      rw [hn, he]
      exact (hΘ₀pol 0).symm
    · rw [hFc]
      simp only
      rw [← hγ1eq, ← hΘ1]
      have hn : (1 - (s:ℝ)) * ‖γ₀ (1 : ↑unitInterval)‖ + (s:ℝ) * ‖γ₀ (1 : ↑unitInterval)‖
          = ‖γ₀ (1 : ↑unitInterval)‖ := by ring
      have he : (1 - (s:ℝ)) * Θ₀ (1 : ↑unitInterval) + (s:ℝ) * Θ₀ (1 : ↑unitInterval)
          = Θ₀ (1 : ↑unitInterval) := by ring
      rw [hn, he]
      exact (hΘ₀pol 1).symm
  refine ⟨⟨fun t => ⟨γ₀ t, hne₀ t, hb₀ t⟩, γ₀.continuous.subtype_mk _⟩,
          ⟨fun t => ⟨γ₁ t, hne₁ t, hb₁ t⟩, γ₁.continuous.subtype_mk _⟩,
          fun t => rfl, fun t => rfl, ⟨?_⟩⟩
  exact
  { toFun := fun st => ⟨Fc st, hFcmem st⟩
    continuous_toFun := hFccont.subtype_mk _
    map_zero_left := fun t => Subtype.ext (hF0 t)
    map_one_left := fun t => Subtype.ext (hF1 t)
    prop' := fun s x hx => Subtype.ext (hFrel s x (by
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr h)) }
