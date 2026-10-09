# SerrePositivity

Verification and Lean 4 formalization of the preprint
**Positivity of Serre's Intersection Multiplicity** (OpenAI, September 23, 2026),
which claims a proof of Serre's positivity conjecture for intersection multiplicities,
including the ramified mixed-characteristic case.

> **Theorem 1.1 (claimed).** Let (R, m) be a regular local ring and M, N nonzero finitely generated
> R-modules with ℓ(M ⊗ N) < ∞ and dim M + dim N = dim R. Then
> χ^R(M, N) = Σᵢ (−1)ⁱ ℓ(Tor_i^R(M, N)) > 0.

## Status

Early stage. Theorem 1.1 and the core case after Lemma 5.1 are stated in `SerrePositivity/Statement.lean` (proofs are `sorry`).

`SerrePositivity/Core/` holds the skeleton of the core case: the data of §5.1 (`CoreData`), the hypotheses making it the paper's data (`CoreData.IsPaperData`), the twisted normalized Euler characteristics `c_σ` of (5.2), the statements of Lemma 5.2 and of (5.18)+(5.17), and a sorry-free proof (`CoreData.chi_pos`) that these give `χ^R(D, E) > 0`. The input bundle `Inputs.Core` packages them as a `Prop`-valued class.

The Lean sources are organized as follows (2026-10-09):

- `Statement.lean`, `EulerChar.lean`: Theorem 1.1 and Serre's intersection multiplicity.
- `HomologicalAlgebra/`: general homological algebra over a ring (basic lemmas on complexes in `Basic`, mapping-cone long exact sequences in `ConeLES`, resolutions indexed by `ℤ` in `Resolution`, base change of complexes, `Tor` and its long exact sequence, K-projective lifts).
- `CommutativeAlgebra/`: general commutative algebra (finite length, modules killed by a power of an ideal, finite local algebras, Hilbert–Samuel multiplicity, Koszul complexes and their exactness, base change and `Tor`, length comparison over a common residue field and along automorphisms, geometric transitivity, sums of homology lengths and truncation of complexes over a local ring).
- `PerfectComplex/`: supported perfect complexes (`Basic`, closure properties in `Support` and `Closure`), their `K₀` (`K0`, functoriality in `K0Functor`), normalized lengths (`NormalizedLength`) and the two Euler evaluations (`NormalizedEuler`, with the ordinary length as the special case `NormalizedLength.ordinary` in `OrdinaryEuler`), and generation of `K₀^{m}(A)` by the Koszul complex (`KoszulGeneration`).
- `Paper/`: the paper's lemmas (`Lemma3_4`, `Lemma3_5` with parts `A_*`, `B_*`, `C_*`).
- `Inputs/`: theorems from outside the paper and standard facts not yet in Mathlib, stated with `sorry` or as classes (Theorem 2.5, Theorem 3.1, facts on regular local rings).
- `Core/`: the core case of §5.

Lemma 3.4 (abstract form), Lemma 3.5b, 3.5c and Lemma 5.2 (`CoreData.firstComparison`, modulo the general inputs of `Inputs/IntersectionTheory.lean`) are proved modulo the inputs; the remaining `sorry` in the paper part is the finiteness step of Lemma 3.5a for the normalized length (`lemma_3_5a_lam_finite`). See `notes/PLAN.md` §12–14.

The plan has three layers:

1. **Paper-specific argument** (§5 and the formal parts of Lemma 3.4/3.5): to be formalized sorry-free first.
2. **New general theorems of the paper** (Theorem 3.1, rational K-theory descent; Theorem 4.7, asymptotic norm comparison): stated as named axioms at first, and checked by hand with priority.
3. **Inputs from the literature** (Serre, Roberts–Gillet–Soulé, Cohen–Gabber, Monsky, Roberts, Cai–Lee–Ma–Schwede–Tucker, Land–Tamme, Bhatt–Scholze): stated as named axioms via `class` + `axiom` instances.

The first milestone is a sorry-free derivation of Theorem 1.1 in which `#print axioms` shows only these named hypotheses.

## Layout

- `paper/` — the preprint and its source (`SOURCE.md`)
- `notes/INVESTIGATION.md` — reading notes, verification checklist, Mathlib survey (in Japanese)
- `notes/MEMO.md` — full investigation memo (in Japanese)
- `notes/PLAN.md` — formalization plan: milestones, file layout, dependency graph, interfaces (in Japanese)
- `SerrePositivity/` — Lean sources

## Source and license

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
