import IwaniecManfredi.Preamble

/-- The modulo-4 contradiction (60) that closes Section 7, and with it the
optimality half of Theorem 1: the identity
`ξ = Σ_{m+n=d} A_{mn}(ξ + εξ^{-3})^m (ξ^{-1} + εξ^3)^n` cannot hold for all
`ξ ≠ 0` when `ε ≠ 0`.  Evaluating at the four fourth roots of `-ε` kills every
factor `ξ + εξ^{-3}` and forces `4 ∣ d+1`; evaluating at the four fourth roots
of `-1/ε` kills every factor `ξ^{-1} + εξ^3` and forces `4 ∣ 3d+1`; and
`(d+1) + (3d+1) = 4d+2` is never divisible by `4`.  Self-contained algebra:
`ε ≠ 0` is the only input, and that is exactly `p ≠ 2`. -/
theorem HomogPolyModFour (eps : ℂ) (heps : eps ≠ 0) (d : ℕ) (hd : 1 ≤ d)
    (A : ℕ → ℕ → ℂ)
    (h60 : ∀ ξ : ℂ, ξ ≠ 0 →
      ξ = ∑ m ∈ Finset.range (d + 1),
            A m (d - m) * (ξ + eps * ξ ^ (-3 : ℤ)) ^ m
              * (ξ ^ (-1 : ℤ) + eps * ξ ^ 3) ^ (d - m)) :
    False := by
  -- Steps 2 and 4 of the .tex each need the two zpow spellings unfolded first
  have hz3 : ∀ ξ : ℂ, ξ ^ (-3 : ℤ) = (ξ ^ 3)⁻¹ := by
    intro ξ; rw [zpow_neg]; norm_num
  have hz1 : ∀ ξ : ℂ, ξ ^ (-1 : ℤ) = ξ⁻¹ := by
    intro ξ; rw [zpow_neg]; norm_num
  -- ## Step 2 + first half of Step 3: evaluation at the fourth roots of -eps
  have key1 : ∀ ξ : ℂ, ξ ≠ 0 → ξ ^ 4 = -eps →
      ξ ^ (d + 1) = A 0 d * (1 - eps ^ 2) ^ d := by
    intro ξ hξ h4
    have hvan : ξ + eps * ξ ^ (-3 : ℤ) = 0 := by
      rw [hz3]; field_simp; linear_combination h4
    have hsnd : ξ ^ (-1 : ℤ) + eps * ξ ^ 3 = ξ⁻¹ * (1 - eps ^ 2) := by
      rw [hz1]; field_simp; linear_combination eps * h4
    have hsum := h60 ξ hξ
    rw [hvan, hsnd] at hsum
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_] at hsum
    · simp only [pow_zero, Nat.sub_zero, mul_one] at hsum
      rw [mul_pow, inv_pow] at hsum
      have hξd : ξ ^ d ≠ 0 := pow_ne_zero _ hξ
      field_simp at hsum
      rw [pow_succ]
      linear_combination hsum
    · intro m _ hm
      rw [zero_pow hm]; ring
  -- ## Step 4 + first half of Step 5: evaluation at the fourth roots of -1/eps
  have key2 : ∀ ξ : ℂ, ξ ≠ 0 → ξ ^ 4 = -eps⁻¹ →
      ξ ^ (3 * d + 1) = A d 0 * ((eps ^ 2 - 1) / eps) ^ d := by
    intro ξ hξ h4
    have hq : eps * ξ ^ 4 = -1 := by
      rw [h4]; field_simp
    have hvan : ξ ^ (-1 : ℤ) + eps * ξ ^ 3 = 0 := by
      rw [hz1]; field_simp; linear_combination hq
    have hfst : ξ + eps * ξ ^ (-3 : ℤ) = (ξ ^ 3)⁻¹ * (eps - eps⁻¹) := by
      rw [hz3]; field_simp; linear_combination hq
    have hsum := h60 ξ hξ
    rw [hvan, hfst] at hsum
    rw [Finset.sum_eq_single_of_mem d (Finset.mem_range.mpr (by omega)) ?_] at hsum
    · simp only [Nat.sub_self, pow_zero, mul_one] at hsum
      rw [mul_pow, inv_pow, ← pow_mul] at hsum
      have hξd : ξ ^ (3 * d) ≠ 0 := pow_ne_zero _ hξ
      field_simp at hsum
      rw [pow_succ]
      linear_combination hsum
    · intro m hm hmd
      have h1 : d - m ≠ 0 := by
        have := Finset.mem_range.mp hm; omega
      rw [zero_pow h1]; ring
  -- ## Step 1: the two fourth roots
  have hI4 : (Complex.I) ^ 4 = 1 := by simp [pow_succ, Complex.I_mul_I]
  have hroot : ∀ z : ℂ, (z ^ (((4 : ℕ) : ℂ))⁻¹) ^ (4 : ℕ) = z := fun z =>
    Complex.cpow_ofNat_inv_pow z 4
  -- ## Step 3: `i^(d+1) = 1`
  have hI1 : (Complex.I) ^ (d + 1) = 1 := by
    have hζ4 : ((-eps) ^ (((4 : ℕ) : ℂ))⁻¹) ^ (4 : ℕ) = -eps := hroot (-eps)
    set ζ : ℂ := (-eps) ^ (((4 : ℕ) : ℂ))⁻¹ with hζdef
    have hζ : ζ ≠ 0 := by
      intro h
      rw [h] at hζ4
      simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hζ4
      exact heps (by linear_combination hζ4)
    have hIζ : (Complex.I * ζ) ^ 4 = -eps := by rw [mul_pow, hI4, one_mul, hζ4]
    have e1 := key1 ζ hζ hζ4
    have e2 := key1 (Complex.I * ζ) (mul_ne_zero Complex.I_ne_zero hζ) hIζ
    have e3 : Complex.I ^ (d + 1) * ζ ^ (d + 1) = 1 * ζ ^ (d + 1) := by
      rw [one_mul, ← mul_pow]
      exact e2.trans e1.symm
    exact mul_right_cancel₀ (pow_ne_zero _ hζ) e3
  -- ## Step 5: `i^(3d+1) = 1`
  have hI2 : (Complex.I) ^ (3 * d + 1) = 1 := by
    have hepsinv : eps⁻¹ ≠ 0 := inv_ne_zero heps
    have hη4 : ((-eps⁻¹) ^ (((4 : ℕ) : ℂ))⁻¹) ^ (4 : ℕ) = -eps⁻¹ := hroot (-eps⁻¹)
    set η : ℂ := (-eps⁻¹) ^ (((4 : ℕ) : ℂ))⁻¹ with hηdef
    have hη : η ≠ 0 := by
      intro h
      rw [h] at hη4
      simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hη4
      exact hepsinv (by linear_combination hη4)
    have hIη : (Complex.I * η) ^ 4 = -eps⁻¹ := by rw [mul_pow, hI4, one_mul, hη4]
    have e1 := key2 η hη hη4
    have e2 := key2 (Complex.I * η) (mul_ne_zero Complex.I_ne_zero hη) hIη
    have e3 : Complex.I ^ (3 * d + 1) * η ^ (3 * d + 1) = 1 * η ^ (3 * d + 1) := by
      rw [one_mul, ← mul_pow]
      exact e2.trans e1.symm
    exact mul_right_cancel₀ (pow_ne_zero _ hη) e3
  -- ## Step 6: the contradiction, with no divisibility arithmetic at all
  have hone : (Complex.I) ^ (4 * d + 2) = 1 := by
    have hexp : (d + 1) + (3 * d + 1) = 4 * d + 2 := by ring
    rw [← hexp, pow_add, hI1, hI2, one_mul]
  have hminus : (Complex.I) ^ (4 * d + 2) = -1 := by
    rw [pow_add, pow_mul, hI4, one_pow, one_mul, Complex.I_sq]
  rw [hminus] at hone
  norm_num at hone
