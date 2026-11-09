import IwaniecManfredi.KAlphaExp

/-- Equation (9) of the paper determines the pair `(k, α)` of Theorem 1
uniquely: for every `1 < p < ∞` there is exactly one pair consisting of an
integer `k ≥ 1` and an exponent `α ∈ (0,1]` with `k + α` equal to the
right-hand side of (9).  Theorem 1 cannot even be stated without this. -/
theorem KAlphaWellDefined (p : ℝ) (hp : 1 < p) :
    ∃! ka : ℕ × ℝ, 1 ≤ ka.1 ∧ 0 < ka.2 ∧ ka.2 ≤ 1 ∧ (ka.1 : ℝ) + ka.2 = KAlphaExp p := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hp1ne : p - 1 ≠ 0 := ne_of_gt hp1
  obtain ⟨q, hqdef⟩ : ∃ x : ℝ, x = 1 / (p - 1) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; exact one_div_pos.mpr hp1
  obtain ⟨v, hvdef⟩ : ∃ x : ℝ, x = KAlphaExp p := ⟨_, rfl⟩
  -- ## Step 1: `6v = 7 + q + sqrt(1 + 14q + q^2)` and hence `v > 4/3 > 1`
  have hrw : 1 + 14 / (p - 1) + 1 / (p - 1) ^ 2 = 1 + 14 * q + q ^ 2 := by
    rw [hqdef]; field_simp
  have hrad : (1 : ℝ) ≤ 1 + 14 * q + q ^ 2 := by nlinarith [sq_nonneg q]
  have hsq : (1 : ℝ) ≤ Real.sqrt (1 + 14 * q + q ^ 2) := Real.one_le_sqrt.mpr hrad
  have h6v : 6 * v = 7 + q + Real.sqrt (1 + 14 * q + q ^ 2) := by
    rw [hvdef, KAlphaExp, hrw, ← hqdef]; ring
  have hv1 : (1 : ℝ) < v := by linarith
  have hv0 : (0 : ℝ) ≤ v := by linarith
  -- ## Step 2: existence, from the ceiling, carried as `⌈v⌉₊ = M + 2`
  have hc : 1 < ⌈v⌉₊ := Nat.lt_ceil.mpr (by push_cast; exact hv1)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ⌈v⌉₊ = M + 2 := ⟨⌈v⌉₊ - 2, by omega⟩
  have hcast : ((⌈v⌉₊ : ℕ) : ℝ) = (M : ℝ) + 2 := by rw [hM]; push_cast; ring
  have hlow : (M : ℝ) + 1 < v := by
    have h := Nat.ceil_lt_add_one hv0
    rw [hcast] at h
    linarith
  have hup : v ≤ (M : ℝ) + 2 := by
    have h := Nat.le_ceil v
    rw [hcast] at h
    exact h
  refine ⟨(M + 1, v - ((M : ℝ) + 1)), ⟨by omega, by linarith, by linarith, ?_⟩, ?_⟩
  · rw [← hvdef]
    push_cast
    ring
  -- ## Step 3: uniqueness, as a two-branch contradiction on `k'`
  · rintro ⟨k', a'⟩ ⟨hk1, ha0, ha1, hsum⟩
    rw [← hvdef] at hsum
    simp only at hsum
    have h1 : ¬ (k' < M + 1) := by
      intro hlt
      have hkm : (k' : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hlt
      linarith
    have h2 : ¬ (M + 1 < k') := by
      intro hgt
      have hkm : (M : ℝ) + 2 ≤ (k' : ℝ) := by
        have hge : M + 2 ≤ k' := by omega
        exact_mod_cast hge
      linarith
    have hk'eq : k' = M + 1 := by omega
    have ha'eq : a' = v - ((M : ℝ) + 1) := by
      rw [hk'eq] at hsum
      push_cast at hsum
      linarith
    rw [hk'eq, ha'eq]
