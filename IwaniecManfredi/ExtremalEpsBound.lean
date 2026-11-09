import IwaniecManfredi.LambdaCoef
import IwaniecManfredi.EpsCoef
import IwaniecManfredi.DExp
import IwaniecManfredi.DExpEqGammaOneInv

/-- The coefficient `ε` of the extremal function (54) of Section 7.  It equals
`ε₂(1,p)`, is given by the formula `(1-d)/(1+3d)` displayed in Section 7,
satisfies the strict bound `|ε| < 1/3`, and vanishes exactly at `p = 2`.  The
bound `|ε| < 1/3` is the quantitative form of the paper's assertion that `H`
of (54) is a quasiconformal homeomorphism of the whole plane, and the
vanishing criterion is its assertion that `ε ≠ 0` precisely because
`p ≠ 2`. -/
theorem ExtremalEpsBound (p : ℝ) (hp : 1 < p) :
    EpsCoef 1 2 p = (1 - DExp p) / (1 + 3 * DExp p) ∧
      |EpsCoef 1 2 p| < 1 / 3 ∧ (EpsCoef 1 2 p = 0 ↔ p = 2) := by
  obtain ⟨hγ0, hγd⟩ := DExpEqGammaOneInv p hp
  obtain ⟨γ, hγdef⟩ : ∃ x : ℝ, x = GammaExp 1 p := ⟨_, rfl⟩
  rw [← hγdef] at hγ0 hγd
  have hγ3 : (0 : ℝ) < γ + 3 := by linarith
  have hγne : γ ≠ 0 := ne_of_gt hγ0
  have hγ3ne : γ + 3 ≠ 0 := ne_of_gt hγ3
  -- ## Step 0: what `ε₂(1,p)` is
  have hLγ : LambdaCoef 1 2 p = γ := by rw [hγdef]; rfl
  have hε : EpsCoef 1 2 p = (γ - 1) / (γ + 3) := by
    rw [EpsCoef, hLγ]
    congr 1 <;> push_cast <;> ring
  -- ## Step 1: the closed form for `γ`, and `γ < 3`
  have hrad : (0 : ℝ) < p ^ 2 + 12 * p - 12 := by nlinarith
  obtain ⟨S, hSdef⟩ : ∃ x : ℝ, x = Real.sqrt (p ^ 2 + 12 * p - 12) := ⟨_, rfl⟩
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = p ^ 2 + 12 * p - 12 := by rw [hSdef]; exact Real.sq_sqrt hrad.le
  have h2γ : 2 * γ = -p + S := by
    rw [hγdef, GammaExp, LambdaCoef, hSdef]
    have h : 4 * (((1 + 1 : ℕ)) : ℝ) ^ 2 * (p - 1) + (((1 : ℕ)) : ℝ) ^ 2 * (p - 2) ^ 2
        = p ^ 2 + 12 * p - 12 := by push_cast; ring
    rw [h]
    push_cast
    ring
  have hγlt3 : γ < 3 := by nlinarith [hS2, hS0]
  -- ## Step 2: assertion (a)
  have hd : DExp p = 1 / γ := by
    field_simp
    linear_combination hγd
  have hdpos : 0 < DExp p := by rw [hd]; exact div_pos one_pos hγ0
  have hdenne : (1 : ℝ) + 3 * DExp p ≠ 0 := ne_of_gt (by linarith)
  have ha : EpsCoef 1 2 p = (1 - DExp p) / (1 + 3 * DExp p) := by
    rw [hε, eq_div_iff hdenne, hd]
    field_simp
  -- ## Step 3: assertion (b)
  have hb : |EpsCoef 1 2 p| < 1 / 3 := by
    rw [hε]
    obtain ⟨E, hEdef⟩ : ∃ y : ℝ, y = (γ - 1) / (γ + 3) := ⟨_, rfl⟩
    rw [← hEdef]
    have hE : E * (γ + 3) = γ - 1 := by
      rw [hEdef]
      field_simp
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · nlinarith [hE, hγ0, hγ3]
    · nlinarith [hE, hγ3, hγlt3]
  -- ## Step 4: assertion (c)
  have hc : EpsCoef 1 2 p = 0 ↔ p = 2 := by
    rw [hε, div_eq_zero_iff]
    constructor
    · intro h
      rcases h with h | h
      · have hSp : S = p + 2 := by linarith
        rw [hSp] at hS2
        ring_nf at hS2
        linarith
      · exact absurd h hγ3ne
    · intro h
      subst h
      left
      have hS4 : S = 4 := by
        have h1 : (S - 4) * (S + 4) = 0 := by linear_combination hS2
        rcases mul_eq_zero.mp h1 with h2 | h2
        · linarith
        · linarith
      linarith
  exact ⟨ha, hb, hc⟩
