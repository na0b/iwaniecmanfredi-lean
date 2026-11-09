import IwaniecManfredi.WindingCalculus
import IwaniecManfredi.WindingAdditivity
import IwaniecManfredi.WindingHomotopyInvariance
import IwaniecManfredi.PunctDiscLoopClass

/-- A homeomorphism of plane domains fixing the origin carries all sufficiently
small circles about the origin to loops of index `±1`.  The hypotheses are
exactly the clauses `QuasiconformalOn` already supplies, so the consumers of
Corollary 1 obtain this from the quasiconformality they already assume; no
quasiregularity, no `W^{1,2}` and no Jacobian is needed.  This is the paper's
step "Applying argument principle, we find that `A_{n+1} ≠ 0`"
(`paper.tex:382`), proved rather than assumed. -/
theorem HomeoCircleIndex (V : Set ℂ) (hV : IsOpen V) (h0 : (0 : ℂ) ∈ V)
    (H chi : ℂ → ℂ) (hHc : ContinuousOn H V) (hHinj : Set.InjOn H V)
    (hHopen : IsOpen (H '' V)) (hchi : ∀ z ∈ V, chi (H z) = z)
    (hchic : ContinuousOn chi (H '' V)) (hH0 : H 0 = 0) :
    ∃ rho > 0, ∀ r : ℝ, 0 < r → r ≤ rho →
      ∀ γ : C(↑unitInterval, ℂ),
        (∀ t : ↑unitInterval,
          γ t = H ((r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I))) →
        ∀ hne : ∀ t, γ t ≠ 0,
          WindingNumber γ hne = 1 ∨ WindingNumber γ hne = -1 := by
  obtain ⟨-, -, hWCc, hWCd⟩ := WindingCalculus
  have hWAb := WindingAdditivity.2
  -- ## Step 0: `chi` is a two-sided inverse on `H '' V`, and the two non-vanishing facts
  have hHval : ∀ w ∈ H '' V, H (chi w) = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hchi z hz]
  have hchine : ∀ w ∈ H '' V, w ≠ 0 → chi w ≠ 0 := by
    intro w hw hw0 hc0
    exact hw0 (by rw [← hHval w hw, hc0, hH0])
  have hHne : ∀ ξ ∈ V, ξ ≠ 0 → H ξ ≠ 0 := by
    intro ξ hξ hξ0 h
    exact hξ0 (hHinj hξ h0 (by rw [h, hH0]))
  -- ## Step 1: choice of `δ` and `rho`
  obtain ⟨δ, hδ0, hδsub⟩ := Metric.isOpen_iff.mp hHopen 0 ⟨0, h0, hH0⟩
  have hWopen : IsOpen (V ∩ H ⁻¹' Metric.ball 0 δ) :=
    hHc.isOpen_inter_preimage hV Metric.isOpen_ball
  have hW0 : (0 : ℂ) ∈ V ∩ H ⁻¹' Metric.ball 0 δ := by
    refine ⟨h0, ?_⟩
    simp only [Set.mem_preimage, hH0, Metric.mem_ball, dist_self]
    exact hδ0
  obtain ⟨ρ', hρ'0, hρ'sub⟩ := Metric.isOpen_iff.mp hWopen 0 hW0
  refine ⟨ρ' / 2, by positivity, ?_⟩
  intro r hr0 hrρ γ hγ hne
  have hclosed : ∀ ξ : ℂ, ‖ξ‖ ≤ ρ' / 2 → ξ ∈ V ∩ H ⁻¹' Metric.ball 0 δ := by
    intro ξ hξ
    refine hρ'sub ?_
    simp only [Metric.mem_ball, dist_zero_right]
    linarith only [hξ, hρ'0]
  -- the model circle: its modulus, and the two reshaped exponentials
  have hexpnorm : ∀ x : ℝ, ‖Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)‖ = 1 := by
    intro x
    have he : (2 : ℂ) * (Real.pi : ℂ) * ((x : ℝ) : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hexpnorm2 : ∀ x y : ℝ,
      ‖Complex.exp (2 * Real.pi * (x : ℝ) * (y : ℝ) * Complex.I)‖ = 1 := by
    intro x y
    have he : (2 : ℂ) * (Real.pi : ℂ) * ((x : ℝ) : ℂ) * ((y : ℝ) : ℂ)
        = ((2 * Real.pi * x * y : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hexp0 : Complex.exp (2 * (Real.pi : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [he, Complex.exp_zero]
  have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I
        = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_two_pi_mul_I]
  have hcnorm : ∀ x : ℝ,
      ‖(r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)‖ = r := by
    intro x
    rw [norm_mul, hexpnorm x, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hcW : ∀ x : ℝ, ((r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I))
      ∈ V ∩ H ⁻¹' Metric.ball 0 δ := by
    intro x
    exact hclosed _ (by rw [hcnorm x]; exact hrρ)
  -- ## Step 2: `γ` is a loop in the punctured disc `B δ - {0}`
  have hγb : ∀ t : ↑unitInterval, ‖γ t‖ < δ := by
    intro t
    rw [hγ t]
    have h := (hcW (t : ℝ)).2
    simpa [Metric.mem_ball, dist_zero_right] using h
  have hrne : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hr0
  have hrV : (r : ℂ) ∈ V := by
    have h := (hcW 0).1
    rwa [hexp0, mul_one] at h
  have hHrne : H (r : ℂ) ≠ 0 := hHne _ hrV hrne
  have hγ0 : γ 0 = H (r : ℂ) := by
    rw [hγ 0, Set.Icc.coe_zero, hexp0, mul_one]
  have hγ1 : γ 1 = H (r : ℂ) := by
    rw [hγ 1, Set.Icc.coe_one, hexp1, mul_one]
  have hloopγ : γ 0 = γ 1 := by rw [hγ0, hγ1]
  have hHrb : ‖H (r : ℂ)‖ < δ := by rw [← hγ0]; exact hγb 0
  -- ## Step 3: the index of `γ` is an integer `d`, and the model loop `ρd`
  obtain ⟨d, hd⟩ := hWCc γ hne hloopγ
  obtain ⟨ρd, hρdapp⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval,
      f t = H (r : ℂ) * Complex.exp (2 * Real.pi * (d : ℝ) * (t : ℝ) * Complex.I) :=
    ⟨⟨fun t => H (r : ℂ) * Complex.exp (2 * Real.pi * (d : ℝ) * (t : ℝ) * Complex.I),
      by fun_prop⟩, fun _ => rfl⟩
  have hρdne : ∀ t, ρd t ≠ 0 := by
    intro t
    rw [hρdapp t]
    exact mul_ne_zero hHrne (Complex.exp_ne_zero _)
  have hρdb : ∀ t : ↑unitInterval, ‖ρd t‖ < δ := by
    intro t
    rw [hρdapp t, norm_mul, hexpnorm2 (d : ℝ) (t : ℝ), mul_one]
    exact hHrb
  have hexpintd : Complex.exp
      (2 * (Real.pi : ℂ) * (((d : ℝ)) : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((d : ℝ)) : ℂ) * (((1 : ℝ)) : ℂ) * Complex.I
        = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
  have hexp0d : Complex.exp
      (2 * (Real.pi : ℂ) * (((d : ℝ)) : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I) = 1 := by
    have he : (2 : ℂ) * (Real.pi : ℂ) * (((d : ℝ)) : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I
        = 0 := by push_cast; ring
    rw [he, Complex.exp_zero]
  have hρd0 : ρd 0 = H (r : ℂ) := by
    rw [hρdapp 0, Set.Icc.coe_zero, hexp0d, mul_one]
  have hρd1 : ρd 1 = H (r : ℂ) := by
    rw [hρdapp 1, Set.Icc.coe_one, hexpintd, mul_one]
  have hρdloop : ρd 0 = ρd 1 := by rw [hρd0, hρd1]
  have hρdind : WindingNumber ρd hρdne = (d : ℝ) :=
    hWCd (H (r : ℂ)) d ρd hρdne hHrne hρdapp
  -- ## Step 4: `γ` and `ρd` are homotopic in the punctured disc
  have hbase : γ 0 = ρd 0 := by rw [hγ0, hρd0]
  have hind : WindingNumber γ hne = WindingNumber ρd hρdne := by rw [hd, hρdind]
  obtain ⟨g₀, g₁, hg₀, hg₁, hhom⟩ :=
    PunctDiscLoopClass δ hδ0 γ ρd hne hρdne hγb hρdb hloopγ hρdloop hbase hind
  -- ## Step 5: transport the homotopy through `chi`
  have hDmem : ∀ w : {z : ℂ // z ≠ 0 ∧ ‖z‖ < δ}, (w : ℂ) ∈ H '' V := by
    intro w
    refine hδsub ?_
    simp only [Metric.mem_ball, dist_zero_right]
    exact w.2.2
  have hcne : ∀ w : {z : ℂ // z ≠ 0 ∧ ‖z‖ < δ}, chi (w : ℂ) ≠ 0 :=
    fun w => hchine _ (hDmem w) w.2.1
  have hccont : Continuous (fun w : {z : ℂ // z ≠ 0 ∧ ‖z‖ < δ} => chi (w : ℂ)) :=
    hchic.comp_continuous continuous_subtype_val hDmem
  obtain ⟨c, hcapp⟩ : ∃ c : C({z : ℂ // z ≠ 0 ∧ ‖z‖ < δ}, {z : ℂ // z ≠ 0}),
      ∀ w, ((c w : ℂ)) = chi (w : ℂ) :=
    ⟨⟨fun w => ⟨chi (w : ℂ), hcne w⟩, hccont.subtype_mk hcne⟩, fun _ => rfl⟩
  -- ## Step 6: the three transported loops, and (12), (13)
  obtain ⟨σ0, hσ0app⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval,
      f t = (r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I) :=
    ⟨⟨fun t => (r : ℂ) * Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I), by fun_prop⟩,
      fun _ => rfl⟩
  have hσ0ne : ∀ t, σ0 t ≠ 0 := by
    intro t
    rw [hσ0app t]
    exact mul_ne_zero hrne (Complex.exp_ne_zero _)
  obtain ⟨σd, hσdapp⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval,
      f t = (((c.comp g₁) t : {z : ℂ // z ≠ 0}) : ℂ) :=
    ⟨⟨fun t => (((c.comp g₁) t : {z : ℂ // z ≠ 0}) : ℂ),
      continuous_subtype_val.comp (c.comp g₁).continuous⟩, fun _ => rfl⟩
  have hσdne : ∀ t, σd t ≠ 0 := by
    intro t
    rw [hσdapp t]
    exact ((c.comp g₁) t).2
  have hcg₀ : ∀ t : ↑unitInterval, (((c.comp g₀) t : {z : ℂ // z ≠ 0}) : ℂ) = σ0 t := by
    intro t
    simp only [ContinuousMap.comp_apply]
    rw [hcapp (g₀ t), hg₀ t, hγ t, hσ0app t]
    exact hchi _ (hcW (t : ℝ)).1
  have hcg₁ : ∀ t : ↑unitInterval, (((c.comp g₁) t : {z : ℂ // z ≠ 0}) : ℂ) = σd t :=
    fun t => (hσdapp t).symm
  have h12 : WindingNumber σ0 hσ0ne = WindingNumber σd hσdne :=
    WindingHomotopyInvariance σ0 σd hσ0ne hσdne (c.comp g₀) (c.comp g₁)
      hcg₀ hcg₁ (hhom.comp_continuousMap c)
  have hexpone : ∀ t : ↑unitInterval,
      (2 : ℂ) * (Real.pi : ℂ) * ((((1 : ℤ) : ℝ)) : ℂ) * ((t : ℝ) : ℂ) * Complex.I
        = 2 * (Real.pi : ℂ) * ((t : ℝ) : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have h13 : WindingNumber σ0 hσ0ne = (((1 : ℤ)) : ℝ) :=
    hWCd (r : ℂ) 1 σ0 hσ0ne hrne (fun t => by rw [hσ0app t, hexpone t])
  -- ## Step 7: the divisibility, through the 1-periodic `psi`
  obtain ⟨ψ, hψapp⟩ : ∃ ψ : ℝ → ℂ, ∀ x : ℝ,
      ψ x = chi (H (r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)) :=
    ⟨_, fun _ => rfl⟩
  have hmodmem : ∀ x : ℝ,
      (H (r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)) ∈ H '' V := by
    intro x
    refine hδsub ?_
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, hexpnorm x, mul_one]
    exact hHrb
  have hmodne : ∀ x : ℝ,
      (H (r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)) ≠ 0 :=
    fun _ => mul_ne_zero hHrne (Complex.exp_ne_zero _)
  have hψc : Continuous ψ := by
    have h : Continuous (fun x : ℝ =>
        H (r : ℂ) * Complex.exp (2 * Real.pi * (x : ℝ) * Complex.I)) := by fun_prop
    refine (hchic.comp_continuous h hmodmem).congr (fun x => ?_)
    simp only [Function.comp_apply, hψapp]
  have hψne : ∀ x, ψ x ≠ 0 := by
    intro x
    rw [hψapp x]
    exact hchine _ (hmodmem x) (hmodne x)
  have hψper : ∀ x, ψ (x + 1) = ψ x := by
    intro x
    have hE : Complex.exp (2 * (Real.pi : ℂ) * (((x + 1 : ℝ)) : ℂ) * Complex.I)
        = Complex.exp (2 * (Real.pi : ℂ) * ((x : ℝ) : ℂ) * Complex.I) := by
      have he : (2 : ℂ) * (Real.pi : ℂ) * (((x + 1 : ℝ)) : ℂ) * Complex.I
          = 2 * (Real.pi : ℂ) * ((x : ℝ) : ℂ) * Complex.I
            + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hψapp (x + 1), hψapp x, hE]
  obtain ⟨σ1, hσ1app⟩ : ∃ f : C(↑unitInterval, ℂ), ∀ t : ↑unitInterval, f t = ψ (t : ℝ) :=
    ⟨⟨fun t => ψ (t : ℝ), hψc.comp continuous_subtype_val⟩, fun _ => rfl⟩
  have hσ1ne : ∀ t, σ1 t ≠ 0 := by
    intro t
    rw [hσ1app t]
    exact hψne _
  have hσdpsi : ∀ t : ↑unitInterval, σd t = ψ ((d : ℝ) * (t : ℝ)) := by
    intro t
    have hE : Complex.exp
          (2 * (Real.pi : ℂ) * (((d : ℝ)) : ℂ) * ((t : ℝ) : ℂ) * Complex.I)
        = Complex.exp
          (2 * (Real.pi : ℂ) * ((((d : ℝ) * (t : ℝ) : ℝ)) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hσdapp t]
    simp only [ContinuousMap.comp_apply]
    rw [hcapp (g₁ t), hg₁ t, hρdapp t, hψapp ((d : ℝ) * (t : ℝ)), hE]
  have h14 : WindingNumber σd hσdne = (d : ℝ) * WindingNumber σ1 hσ1ne :=
    hWAb ψ hψc hψne hψper d σ1 σd hσ1ne hσdne hσ1app hσdpsi
  -- ## Step 8: `1 = d e`, hence `d = ±1`
  have hσ1loop : σ1 0 = σ1 1 := by
    rw [hσ1app 0, hσ1app 1, Set.Icc.coe_zero, Set.Icc.coe_one,
      hψapp (0 : ℝ), hψapp (1 : ℝ), hexp0, hexp1]
  obtain ⟨e, he⟩ := hWCc σ1 hσ1ne hσ1loop
  have h1de : (((1 : ℤ)) : ℝ) = ((d * e : ℤ) : ℝ) := by
    rw [← h13, h12, h14, he]
    push_cast
    ring
  have hde : d * e = 1 := by exact_mod_cast h1de.symm
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hde with ⟨hd1, -⟩ | ⟨hd1, -⟩
  · left
    rw [hd, hd1]
    norm_num
  · right
    rw [hd, hd1]
    norm_num
