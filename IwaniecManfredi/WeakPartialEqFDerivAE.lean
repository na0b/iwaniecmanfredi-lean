import IwaniecManfredi.MemLpLocOn
import IwaniecManfredi.IsWeakPartialOn
import IwaniecManfredi.PartialWord
import IwaniecManfredi.WeakPartialDiffQuotientAe

/-- The bridge between the two notions of derivative the tablet carries: if
`u` and the family `D` are locally integrable on an open set and `D j` is the
*distributional* `j`-th partial derivative of `u` there, and if `u` happens to
be differentiable at almost every point, then `D j` agrees almost everywhere
with the *classical* partial derivative `∂_j u = PartialWord [j] u`.

`QuasiregularOn` and `MemWLocOn` are written with `IsWeakPartialOn`, which is
the integration-by-parts identity, while `DZ`, `DZbar`, `HRad`, `HAng` and
`PartialWord` are all built from `fderiv ℝ`; nothing in the tablet related the
two, which is why so many nodes carried a `C^∞` hypothesis on `H` instead.
This is that missing brick.  The hypotheses are exactly what a `W^{1,1}_loc`
witness supplies -- take `D j := D [j]` for the family `D` of `MemWLocOn 1 1`
-- together with the almost-everywhere differentiability that `QCPackage`'s
`qc_inverse` clause gives for the inverse of a quasiconformal map. -/
theorem WeakPartialEqFDerivAE (Ω : Set ℂ) (hΩ : IsOpen Ω) (u : ℂ → ℂ)
    (D : Fin 2 → (ℂ → ℂ))
    (hu : MemLpLocOn 1 Ω u)
    (hD : ∀ j : Fin 2, MemLpLocOn 1 Ω (D j))
    (hweak : ∀ j : Fin 2, IsWeakPartialOn Ω j u (D j))
    (hdiff : ∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ u z) :
    ∀ j : Fin 2, ∀ᵐ z : ℂ, z ∈ Ω → D j z = PartialWord [j] u z := by
  -- Step 0: a countable exhaustion of `Ω` by compact subsets.
  obtain ⟨K, hKc, hKsub, hKunion⟩ :
      ∃ K : ℕ → Set ℂ, (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ Ω) ∧ Ω ⊆ ⋃ m, K m := by
    refine ⟨fun m => Metric.closedBall 0 (m : ℝ) ∩ (Metric.thickening (1 / ((m : ℝ) + 1)) Ωᶜ)ᶜ,
      fun m => (isCompact_closedBall _ _).inter_right
        (Metric.isOpen_thickening.isClosed_compl), ?_, ?_⟩
    · intro m z hz
      by_contra hzΩ
      exact hz.2 (Metric.self_subset_thickening (by positivity) Ωᶜ hzΩ)
    · intro z hz
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
      refine Set.mem_iUnion.mpr ⟨max ⌈‖z‖⌉₊ ⌈1 / ε⌉₊, ?_, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right]
        refine le_trans (Nat.le_ceil ‖z‖) ?_
        exact_mod_cast Nat.cast_le.mpr (le_max_left _ _)
      · intro hmem
        obtain ⟨w, hw, hdw⟩ := Metric.mem_thickening_iff.mp hmem
        have hce : (1 : ℝ) / ε ≤ ((max ⌈‖z‖⌉₊ ⌈1 / ε⌉₊ : ℕ) : ℝ) := by
          refine le_trans (Nat.le_ceil ((1 : ℝ) / ε)) ?_
          exact_mod_cast Nat.cast_le.mpr (le_max_right _ _)
        have hlt : 1 / (((max ⌈‖z‖⌉₊ ⌈1 / ε⌉₊ : ℕ) : ℝ) + 1) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          have h1 : (1 : ℝ) ≤ ((max ⌈‖z‖⌉₊ ⌈1 / ε⌉₊ : ℕ) : ℝ) * ε :=
            (div_le_iff₀ hε).mp hce
          nlinarith [h1, hε]
        refine hw (hball ?_)
        rw [Metric.mem_ball, dist_comm]
        exact lt_trans hdw hlt
  intro j
  -- Steps 6 and 7: identify the two limits of the difference quotients.
  have key : ∀ m : ℕ, ∀ᵐ z : ℂ, z ∈ K m → D j z = PartialWord [j] u z := by
    intro m
    obtain ⟨t, ht0, htlim, hae⟩ :=
      WeakPartialDiffQuotientAe Ω hΩ j u (D j) hu (hD j) (hweak j) (K m) (hKc m) (hKsub m)
    have htW : Filter.Tendsto t Filter.atTop (nhdsWithin 0 ({(0 : ℝ)}ᶜ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t htlim
        (Filter.Eventually.of_forall (fun l => ht0 l))
    filter_upwards [hae, hdiff] with z hz1 hz2
    intro hzK
    have hdz : DifferentiableAt ℝ u z := hz2 (hKsub m hzK)
    -- Step 6: the classical derivative is the limit of the same quotients.
    have hline : HasDerivAt
        (fun s : ℝ => z + s • (if j = 0 then (1 : ℂ) else Complex.I))
        (if j = 0 then (1 : ℂ) else Complex.I) 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).smul_const
          (if j = 0 then (1 : ℂ) else Complex.I)).const_add z
    have hd : HasDerivAt (fun s : ℝ => u (z + s • (if j = 0 then (1 : ℂ) else Complex.I)))
        (fderiv ℝ u z (if j = 0 then (1 : ℂ) else Complex.I)) 0 := by
      have h0 : z = (fun s : ℝ => z + s • (if j = 0 then (1 : ℂ) else Complex.I)) 0 := by
        simp
      have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq
        (l := u) (f := fun s : ℝ => z + s • (if j = 0 then (1 : ℂ) else Complex.I))
        (hl := hdz.hasFDerivAt) (hf := hline) (hy := h0)
      simpa [Function.comp_def] using hcomp
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hcomp := hd.comp htW
    have hslope : (fun l => slope
          (fun s : ℝ => u (z + s • (if j = 0 then (1 : ℂ) else Complex.I))) 0 (t l))
        = fun l => (t l)⁻¹ •
            (u (z + t l • (if j = 0 then (1 : ℂ) else Complex.I)) - u z) := by
      funext l
      simp [slope]
    rw [Function.comp_def, hslope] at hcomp
    -- Step 7: a sequence of complex numbers has at most one limit.
    have := tendsto_nhds_unique (hz1 hzK) hcomp
    simpa [PartialWord] using this
  -- Step 8: a countable union of null sets is null.
  filter_upwards [MeasureTheory.ae_all_iff.mpr key] with z hz hzΩ
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hKunion hzΩ)
  exact hz m hm
