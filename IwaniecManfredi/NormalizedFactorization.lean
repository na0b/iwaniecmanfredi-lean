import IwaniecManfredi.QCPackage
import IwaniecManfredi.SmoothOffZeros
import IwaniecManfredi.ChiSmoothOffZero

/-- Section 3's normalised form of the factorization (15): near a zero `z₀` of
a solution of (12) which does not vanish identically, the factorization
`g = χ^m` may be taken on a neighbourhood `V'` on which `χ` is `C^∞` off `z₀`,
and whose inverse `H` is continuous on `χ(V')`, inverts `χ` on both sides and
sends `0` to `z₀`.

The factorization is asserted of the continuous representative `g` of the
quasiregular `f`, and the equation and the singular point are read for `g`
too.  They must be: `QuasiregularOn` sees `f` only almost everywhere, so a
pointwise identity `f = χ^m` on an open set is not implied by any hypothesis
on `f` alone, and `f⁻¹(0)` is not determined modulo null sets.  This is the
same reading of (C2) and (C3) that `QCPackage` and `SmoothOffZeros` carry, and
a single representative is threaded through all of them.

No smoothness of `H` is claimed, and none is available here: the paper's arrow
runs `H → χ` (`paper.tex:416`), and `H`'s regularity off the origin is produced
downstream by `Cor1` from the expansion (19), as at `paper.tex:387-388`.  Nor
is anything else about `H` claimed: its `W^{1,2}_loc` membership, almost
everywhere differentiability and `Jac H > 0` almost everywhere are one
application of (C2)'s inverse clause away, and its quasiconformality and
equation (18) are assembled from those inside `Cor2`, which is where `Cor1` is
applied and which already carries the bundle (C2) and the `χ` data. -/
theorem NormalizedFactorization (p : ℝ) (K : ℝ) (hp : 1 < p)
    (qcp : QCPackage) (soz : SmoothOffZeros)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (f g : ℂ → ℂ) (hqr : QuasiregularOn K Ω f)
    (hg : ∀ᵐ z : ℂ, z ∈ Ω → g z = f z) (hgc : ContinuousOn g Ω)
    (hgd : ∀ᵐ z : ℂ, z ∈ Ω → DifferentiableAt ℝ g z)
    (h12 : SolvesEq12 p Ω g)
    (hne : ∃ z ∈ Ω, g z ≠ 0)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) (hf0 : g z₀ = 0) :
    ∃ (m : ℕ) (K' : ℝ) (V' : Set ℂ) (chi H : ℂ → ℂ),
      1 ≤ m ∧ 1 ≤ K' ∧ IsOpen V' ∧ z₀ ∈ V' ∧ V' ⊆ Ω ∧
      QuasiconformalOn K' V' chi ∧ chi z₀ = 0 ∧ (∀ z ∈ V', g z = chi z ^ m) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) chi (V' \ {z₀}) ∧
      (∀ z ∈ V', H (chi z) = z) ∧ ContinuousOn H (chi '' V') ∧
      H 0 = z₀ ∧ (∀ ξ ∈ chi '' V', H ξ ∈ V' ∧ chi (H ξ) = ξ) := by
  -- ## Step 1: the factorization (1) and the isolated zero (3)
  obtain ⟨m, K', V₀, chi, hm, hV₀o, hz₀V₀, hV₀Ω, hqc, hchi0, hfactor⟩ :=
    qcp.qr_factorization K Ω f g z₀ hΩ hconn hqr hg hgc hne hz₀ hf0
  obtain ⟨hqrchi, hinj, hchic, himgopen, psi, hpsi, hpsic⟩ := hqc
  obtain ⟨hK'1, hMW, a, b, hab, hdist⟩ := hqrchi
  obtain ⟨r₀, hr₀, hzeros⟩ :=
    qcp.qr_discrete_zeros K Ω f g hΩ hconn hqr hg hgc hne z₀ hz₀
  -- ## Step 2: the neighbourhood `V'`
  obtain ⟨V', hV'def⟩ : ∃ S : Set ℂ, S = V₀ ∩ Metric.ball z₀ r₀ := ⟨_, rfl⟩
  have hV'o : IsOpen V' := by rw [hV'def]; exact hV₀o.inter Metric.isOpen_ball
  have hz₀V' : z₀ ∈ V' := by rw [hV'def]; exact ⟨hz₀V₀, Metric.mem_ball_self hr₀⟩
  have hV'V₀ : V' ⊆ V₀ := by rw [hV'def]; exact Set.inter_subset_left
  have hV'Ω : V' ⊆ Ω := hV'V₀.trans hV₀Ω
  -- (4): `z₀` is the only zero of `g` in `V'`
  have hgne : ∀ z ∈ V' \ {z₀}, g z ≠ 0 := by
    intro z hz
    have hzb : z ∈ Metric.ball z₀ r₀ := by
      have hz1 := hz.1
      rw [hV'def] at hz1
      exact hz1.2
    exact hzeros z (hV'Ω hz.1) (by simpa using hz.2) (Metric.mem_ball.mp hzb)
  -- ## Step 3: the five clauses of `QuasiconformalOn` restrict from `V₀` to `V'`
  -- (3a) the three restriction primitives: every compact subset of `V'` is one of `V₀`,
  -- every test function for `V'` is one for `V₀`, and the integral identity sees no set
  have hMLres : ∀ (s : ENNReal) (u : ℂ → ℂ), MemLpLocOn s V₀ u → MemLpLocOn s V' u :=
    fun s u h Kc hKsub hKc => h Kc (hKsub.trans hV'V₀) hKc
  have htf : ∀ φ : ℂ → ℂ, IsTestFn V' φ → IsTestFn V₀ φ :=
    fun φ h => ⟨h.1, h.2.1, h.2.2.trans hV'V₀⟩
  have hWPres : ∀ (j : Fin 2) (u v : ℂ → ℂ),
      IsWeakPartialOn V₀ j u v → IsWeakPartialOn V' j u v :=
    fun j u v h φ hφ => h φ (htf φ hφ)
  have hWres : ∀ (u a' b' : ℂ → ℂ),
      IsWeakWirtingerOn V₀ u a' b' → IsWeakWirtingerOn V' u a' b' := by
    intro u a' b' hw
    obtain ⟨ux, uy, h1, h2, h3, h4, h5, h6, h7⟩ := hw
    exact ⟨ux, uy, hMLres 1 u h1, hMLres 1 ux h2, hMLres 1 uy h3,
      hWPres 0 u ux h4, hWPres 1 u uy h5, h6, h7⟩
  have hWLres : ∀ (k : ℕ) (s : ENNReal) (u : ℂ → ℂ),
      MemWLocOn k s V₀ u → MemWLocOn k s V' u := by
    intro k s u hu
    obtain ⟨D, hD0, hDL, hDP⟩ := hu
    exact ⟨D, hD0, fun w hw => hMLres s (D w) (hDL w hw),
      fun w j hw => hWPres j (D w) (D (w ++ [j])) (hDP w j hw)⟩
  have hqrchi' : QuasiregularOn K' V' chi :=
    ⟨hK'1, hWLres 1 2 chi hMW, a, b, hWres chi a b hab,
      hdist.mono (fun z hz hzV' => hz (hV'V₀ hzV'))⟩
  -- (3c) the image identity (6), and openness through the continuity of `psi`
  have himg : chi '' V' = chi '' V₀ ∩ psi ⁻¹' V' := by
    refine Set.eq_of_subset_of_subset (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · obtain ⟨z, hz, rfl⟩ := hξ
      refine ⟨⟨z, hV'V₀ hz, rfl⟩, ?_⟩
      rw [Set.mem_preimage, hpsi z (hV'V₀ hz)]
      exact hz
    · obtain ⟨⟨y, hy, hyeq⟩, hpre⟩ := hξ
      rw [Set.mem_preimage, ← hyeq, hpsi y hy] at hpre
      exact ⟨y, hpre, hyeq⟩
  have himg'open : IsOpen (chi '' V') := by
    rw [himg]
    exact hpsic.isOpen_inter_preimage himgopen hV'o
  -- ## Step 4: `g` is `C^∞` on `V' - {z₀}`
  have hsm := soz.smooth_off_zeros p Ω f g hΩ hp hqr.2.1 hg hgc hgd h12
  have hgsm : ContDiffOn ℝ (⊤ : ℕ∞) g (V' \ {z₀}) :=
    hsm.mono (fun z hz => ⟨hV'Ω hz.1, fun hz0 => hgne z hz hz0⟩)
  -- ## Step 5: `chi` is `C^∞` on `V' - {z₀}`, by `ChiSmoothOffZero`
  have hchism : ContDiffOn ℝ (⊤ : ℕ∞) chi (V' \ {z₀}) :=
    ChiSmoothOffZero m hm (V' \ {z₀}) (hV'o.sdiff isClosed_singleton) g chi
      (hchic.mono (fun z hz => hV'V₀ hz.1))
      (fun z hz => hfactor z (hV'V₀ hz.1)) hgsm hgne
  -- ## Steps 6 and 7: `H = psi`, with its three consequences
  refine ⟨m, K', V', chi, psi, hm, hK'1, hV'o, hz₀V', hV'Ω,
    ⟨hqrchi', hinj.mono hV'V₀, hchic.mono hV'V₀, himg'open,
      psi, fun z hz => hpsi z (hV'V₀ hz), hpsic.mono (Set.image_mono hV'V₀)⟩,
    hchi0, fun z hz => hfactor z (hV'V₀ hz), hchism,
    fun z hz => hpsi z (hV'V₀ hz), hpsic.mono (Set.image_mono hV'V₀), ?_, ?_⟩
  · rw [← hchi0]
    exact hpsi z₀ hz₀V₀
  · intro ξ hξ
    obtain ⟨z, hz, rfl⟩ := hξ
    rw [hpsi z (hV'V₀ hz)]
    exact ⟨hz, rfl⟩
