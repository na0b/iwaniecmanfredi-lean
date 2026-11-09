import IwaniecManfredi.QuasiconformalOn
import IwaniecManfredi.MemWLocOn
import IwaniecManfredi.Jac

/-- The hypothesis bundle (C2) of the paper's note for the formalization: the
results of [Ah], [LV] quoted without proof about quasiregular mappings --
continuity, discreteness of the zero set, the factorization `f = χ^n` near a
zero, and the `W^{1,2}_loc`, almost-everywhere differentiability and `J > 0`
properties of the inverse of a quasiconformal homeomorphism.  Per
`paper/paper.tex:103` this is carried as an explicit hypothesis, never as an
axiom.  Equation (17), the remaining clause of the quoted (C2), is not assumed
here: it is proved in the tablet from the Wirtinger chain rule.

The first three clauses speak of a *representative*: `QuasiregularOn` is a
property of the almost-everywhere class of `f` and of nothing more, since it
sees `f` through `MemWLocOn`, a family of integral identities and indicator
`MemLp` conditions, and through an almost-everywhere inequality between the
*weak* Wirtinger derivatives of `f`, which depend only on that class.  So it
cannot constrain `f` at any single point.  Asserting continuity of `f` itself
would therefore make the bundle uninhabited -- the function which is `1` at
the origin and `0` elsewhere is `1`-quasiregular on `ℂ`, its weak derivatives
being those of the zero function, and it is discontinuous -- and
`paper.tex:107` forbids vacuous quoted results.  The weak reading of the
distortion inequality is what makes `qr_continuous` true: read for the
pointwise derivatives of the given representative it would be satisfied by
classes with no continuous representative whatever, such as
`log log (1/|z|)` perturbed on a dense null set.
So `qr_continuous` produces a continuous `g` equal to `f` almost everywhere,
and the next two clauses take that `g` and speak about it; its zero set is
`g⁻¹(0)`, which is the set the paper writes as `f⁻¹(0) = {z : ∇u(z) = 0}` at
`paper.tex:156`.  Only `qr_continuous` produces a representative, so a
consumer introduces one `g` and runs on it throughout.  `qc_inverse` needs no
such repair: its hypotheses constrain `chi` through `QuasiconformalOn`, which
carries pointwise content, and its three conclusions are themselves
almost-everywhere statements. -/
structure QCPackage where
  qr_continuous :
    ∀ (K : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ), IsOpen Ω → QuasiregularOn K Ω f →
      ∃ g : ℂ → ℂ, (∀ᵐ z : ℂ, z ∈ Ω → g z = f z) ∧ ContinuousOn g Ω
  qr_discrete_zeros :
    ∀ (K : ℝ) (Ω : Set ℂ) (f g : ℂ → ℂ), IsOpen Ω → IsConnected Ω →
      QuasiregularOn K Ω f →
      (∀ᵐ z : ℂ, z ∈ Ω → g z = f z) → ContinuousOn g Ω →
      (∃ z ∈ Ω, g z ≠ 0) →
      ∀ z₀ ∈ Ω, ∃ r > 0, ∀ z ∈ Ω, z ≠ z₀ → dist z z₀ < r → g z ≠ 0
  qr_factorization :
    ∀ (K : ℝ) (Ω : Set ℂ) (f g : ℂ → ℂ) (z₀ : ℂ), IsOpen Ω → IsConnected Ω →
      QuasiregularOn K Ω f →
      (∀ᵐ z : ℂ, z ∈ Ω → g z = f z) → ContinuousOn g Ω →
      (∃ z ∈ Ω, g z ≠ 0) → z₀ ∈ Ω → g z₀ = 0 →
      ∃ (n : ℕ) (K' : ℝ) (V : Set ℂ) (chi : ℂ → ℂ),
        1 ≤ n ∧ IsOpen V ∧ z₀ ∈ V ∧ V ⊆ Ω ∧
        QuasiconformalOn K' V chi ∧ chi z₀ = 0 ∧ ∀ z ∈ V, g z = chi z ^ n
  qc_inverse :
    ∀ (K : ℝ) (V : Set ℂ) (chi Hm : ℂ → ℂ), IsOpen V → QuasiconformalOn K V chi →
      (∀ z ∈ V, Hm (chi z) = z) →
      MemWLocOn 1 2 (chi '' V) Hm ∧
      (∀ᵐ ξ, ξ ∈ chi '' V → DifferentiableAt ℝ Hm ξ) ∧
      (∀ᵐ ξ, ξ ∈ chi '' V → 0 < Jac Hm ξ)
