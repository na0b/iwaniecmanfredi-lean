# Regularity of p-harmonic functions on the plane, in Lean 4

This repository contains a Lean 4 formalization of the theorems, corollaries and lemmas of the article below. It is built on [Mathlib](https://github.com/leanprover-community/mathlib4).

> Tadeusz Iwaniec and Juan J. Manfredi,
> *Regularity of p-harmonic functions on the plane*,
> Revista Matemática Iberoamericana **5** (1989), no. 1–2, 1–19.

Theorem 1 determines the exact regularity of p-harmonic functions in the plane. If k + α is the exponent of equation (9) of the article, with k ≥ 1 an integer and 0 < α ≤ 1, then a p-harmonic function belongs to C<sup>k,α</sup><sub>loc</sub> and to W<sup>k+2,q</sup><sub>loc</sub> for 1 ≤ q < 2/(2−α). For p ≠ 2 this is optimal.

**Three groups of results that the article quotes from the literature are not proved.** They are stated precisely and taken as explicit hypotheses; see [Cited results](#cited-results). Only `Thm1Regularity` and `Cor2` use them. The optimality assertion of Theorem 1, including the extremal function of Section 7, uses none of them. Everything else is proved.

The development contains no `sorry` and no axioms. Each of the eight results depends only on the three standard axioms of Lean: `propext`, `Classical.choice` and `Quot.sound`.

<!-- TODO: remove once the statements below have been read against the article. -->

## Results

| Article | Lean declaration | File |
|---|---|---|
| Theorem 1, regularity | `Thm1Regularity` | [`IwaniecManfredi/Thm1Regularity.lean`](IwaniecManfredi/Thm1Regularity.lean) |
| Theorem 1, optimality | `Thm1Optimality` | [`IwaniecManfredi/Thm1Optimality.lean`](IwaniecManfredi/Thm1Optimality.lean) |
| Corollary 1 | `Cor1` | [`IwaniecManfredi/Cor1.lean`](IwaniecManfredi/Cor1.lean) |
| Corollary 2 | `Cor2` | [`IwaniecManfredi/Cor2.lean`](IwaniecManfredi/Cor2.lean) |
| Theorem 2, expansion | `Thm2Expansion` | [`IwaniecManfredi/Thm2Expansion.lean`](IwaniecManfredi/Thm2Expansion.lean) |
| Theorem 2, converse | `Thm2Converse` | [`IwaniecManfredi/Thm2Converse.lean`](IwaniecManfredi/Thm2Converse.lean) |
| Lemma 1 | `Lemma1` | [`IwaniecManfredi/Lemma1.lean`](IwaniecManfredi/Lemma1.lean) |
| Lemma 2 | `Lemma2` | [`IwaniecManfredi/Lemma2.lean`](IwaniecManfredi/Lemma2.lean) |

The formalization follows a LaTeX transcription of the scanned article, in which the following misprints were corrected: 2k → 2π in (30); a missing bar on A<sub>k</sub> in (40); (p−2)² → (p−1)² in (50); the index of the class ℙ on p. 13; and "v =" → "v ∈" on p. 16.

## Definitions

| Article | Lean | Meaning |
|---|---|---|
| p-harmonic u ∈ W<sup>1,p</sup><sub>loc</sub>(Ω) | `PHarmonicOn p Ω u` | u and a weak gradient g are in L<sup>p</sup><sub>loc</sub>, and ∫ \|g\|<sup>p−2</sup>⟨g, ∇φ⟩ = 0 for all test functions φ |
| W<sup>k,s</sup><sub>loc</sub>(Ω) | `MemWLocOn k s Ω u` | all weak partial derivatives of order at most k exist and are in L<sup>s</sup><sub>loc</sub> |
| C<sup>k,α</sup><sub>loc</sub>(Ω) | `MemHolderLocOn k α Ω u` | C<sup>k</sup>, with k-th derivative α-Hölder on compact subsets |
| C<sup>k+α</sup><sub>loc</sub>(Ω) | `MemHolderSmallOn k α Ω u` | see below |
| exponent of (9) | `KAlphaExp p` | (7 + 1/(p−1) + √(1 + 14/(p−1) + 1/(p−1)²)) / 6 |
| K-quasiregular | `QuasiregularOn K Ω f` | f ∈ W<sup>1,2</sup><sub>loc</sub> and the distortion inequality holds a.e. for the weak Wirtinger derivatives |
| K-quasiconformal | `QuasiconformalOn K Ω χ` | quasiregular, injective, continuous, open image, continuous inverse |
| equations (12), (18) | `SolvesEq12`, `SolvesEq18` | a.e., for the weak Wirtinger derivatives |

Points where the Lean statement makes a choice the reader should check:

- **Representatives.** `PHarmonicOn` concerns a function known up to null sets. `Thm1Regularity` therefore asserts the existence of a representative w, equal to u almost everywhere, with the stated regularity.
- **The class C<sup>k+α</sup><sub>loc</sub>.** The article defines it as a closure of C<sup>∞</sup>. `MemHolderSmallOn` uses the intrinsic description of that closure: the little-Hölder condition for α < 1 and C<sup>k+1</sup> for α = 1. In `Thm1Optimality` this class is what the extremal function fails to belong to.
- **Domains.** A domain is an open connected subset of ℂ (`IsOpen`, `IsConnected`).
- **Theorem 2.** `Thm2Expansion` assumes that H is continuous on the unit disc, differentiable almost everywhere, in W<sup>1,2</sup><sub>loc</sub>, a solution of (18), and of finite energy. These replace the standing assumption of Section 3 that H be C<sup>∞</sup> off the origin, which is not needed in this form. The converse `Thm2Converse` constructs H and concludes that it is continuous and C<sup>∞</sup> off the origin.
- **Corollary 2.** The factorization f = χ<sup>n</sup> near the zero, the smoothness of χ off the origin and the inverse H are hypotheses of `Cor2`; `QCPackage` supplies the remaining facts about H.

## Theorem 1

```lean
theorem Thm1Regularity (p : ℝ) (hp : 1 < p) (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α ≤ 1) (hka : (k : ℝ) + α = KAlphaExp p)
    (cgp : CGradPackage) (qcp : QCPackage) (soz : SmoothOffZeros)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (u : ℂ → ℝ) (hu : PHarmonicOn p Ω u) :
    ∃ w : ℂ → ℝ,
      (∀ᵐ z, z ∈ Ω → w z = u z) ∧
      MemHolderLocOn k α Ω (fun z => ((w z : ℝ) : ℂ)) ∧
      (∀ q : ℝ, 1 ≤ q → q < 2 / (2 - α) →
        MemWLocOn (k + 2) (ENNReal.ofReal q) Ω (fun z => ((w z : ℝ) : ℂ))) := ...
```

```lean
theorem Thm1Optimality (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α ≤ 1) (hka : (k : ℝ) + α = KAlphaExp p)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsConnected Ω) :
    ∃ v : ℂ → ℝ,
      PHarmonicOn p Ω v ∧
      ContinuousOn (fun z => ((v z : ℝ) : ℂ)) Ω ∧
      ¬ MemHolderSmallOn k α Ω (fun z => ((v z : ℝ) : ℂ)) ∧
      ¬ MemWLocOn (k + 2) (ENNReal.ofReal (2 / (2 - α))) Ω
        (fun z => ((v z : ℝ) : ℂ)) := ...
```

## Cited results

The cited results are structures, stated in the file of the same name. No axiom is introduced.

| Literature (as quoted in the article) | Lean hypothesis | Content |
|---|---|---|
| Bojarski–Iwaniec; Manfredi 1988 | `CGradPackage` | the complex gradient f of a p-harmonic function is in W<sup>1,2</sup><sub>loc</sub>, solves (12) and is K-quasiregular with K = max(p−1, 1/(p−1)); a continuous representative of f is differentiable a.e. and solves (12) pointwise a.e. |
| Ahlfors; Lehto–Virtanen | `QCPackage` | a quasiregular map has a continuous representative; its zeros are discrete unless it vanishes identically; near a zero it factors as χ<sup>n</sup> with χ quasiconformal; the inverse of a quasiconformal map is in W<sup>1,2</sup><sub>loc</sub>, differentiable a.e., with positive Jacobian a.e. |
| General elliptic regularity, as used in Section 2 | `SmoothOffZeros` | a continuous W<sup>1,2</sup><sub>loc</sub> solution of (12), differentiable a.e., is C<sup>∞</sup> off its zero set |

Each hypothesis was reviewed during the formalization for two things: that it is not stronger than the cited result, and that it is not vacuous. An early version of the definition of quasiregularity used classical derivatives of a given representative, which made `QCPackage` false; this was caught at the human review gate and corrected to weak derivatives before the proofs were written.

## What is and is not checked by Lean

The Lean kernel checks that each result follows from Mathlib, the definitions and the stated hypotheses, using only the three standard axioms. Lean does **not** check:

- that the cited results hold: they are taken from the literature, as in the article;
- that the definitions and statements say what the article says.

The statements were reviewed against the article during the formalization; see [How this formalization was produced](#how-this-formalization-was-produced). Readers who rely on the results should still compare them against the article themselves, together with the definitions they use. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration. These are cross-referenced to the article and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) (196 pages). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> iwaniecmanfredi-lean
cd iwaniecmanfredi-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by the eight results
```

The project is pinned to Lean `v4.33.0` and to the Mathlib commit recorded in `lakefile.lean`. On every push, continuous integration rebuilds the project and checks the axioms.

## Layout

```
IwaniecManfredi.lean     root module, imports the eight results
IwaniecManfredi/         one file per definition, lemma or theorem (123 files)
Axioms.lean              #print axioms for the eight results
blueprint/blueprint.tex  natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline. AI agents (Claude, by Anthropic) wrote the Lean proofs and the blueprint under the Trellis protocol. Each node was reviewed automatically on three counts:

- the soundness of its natural-language proof;
- its faithfulness to the article;
- the agreement between its Lean statement and its natural-language statement.

Juan J. Manfredi chose the targets, decided which cited results are carried as hypotheses, and approved the statements at the Trellis gates. The Lean kernel checks every proof.

**Review status.** The Lean statements and definitions have been read against the article by J. J. Manfredi. They have not yet been reviewed by T. Iwaniec.

## Citation

Please cite the article; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
