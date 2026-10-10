# SerrePositivity

Verification and Lean 4 formalization of the preprint
**Positivity of Serre's Intersection Multiplicity** (OpenAI, September 23, 2026),
which claims a proof of Serre's positivity conjecture for intersection multiplicities,
including the ramified mixed-characteristic case.

> **Theorem 1.1 (claimed).** Let (R, m) be a regular local ring and M, N nonzero finitely generated
> R-modules with ℓ(M ⊗ N) < ∞ and dim M + dim N = dim R. Then
> χ^R(M, N) = Σᵢ (−1)ⁱ ℓ(Tor_i^R(M, N)) > 0.

## Status

Early stage. Theorem 1.1 and the core case after Lemma 5.1 are stated in `SerrePositivity/Paper/Statement.lean` (proofs are `sorry`).

`SerrePositivity/Paper/Section5/` contains the twisted Euler evaluations, the application of Lemma 3.5, and the final positivity argument. Lemma 5.2 (`firstComparison` in `Paper/Lemma5_2.lean`) takes its rings, finite algebras, ranks, parameters, group action, and length conditions as explicit arguments. The former `CoreData`, `IsPaperData`, and `Inputs.Core` bundles have been removed. `core_of_inputs` applies Lemma 5.2 to supplied data and combines it with an explicitly supplied second comparison; it does not construct those data or prove the second comparison. Ranks are written directly as `Module.finrank`.

The Lean sources are organized as follows (2026-10-10):

- `HomologicalAlgebra/`: general homological algebra over a ring (basic lemmas on complexes and finite free terms in `Basic`, mapping-cone long exact sequences in `ConeLES`, resolutions indexed by `ℤ` in `Resolution`, base change of complexes, `Tor` with resolution computations and annihilator actions, its long exact sequence, scalar null-homotopies (`NullHomotopy`), K-projective lifts).
- `CommutativeAlgebra/`: general commutative algebra (finite length, modules killed by a power of an ideal, finite local algebras, Hilbert–Samuel multiplicity, Koszul complexes and base change (`Koszul`), exactness, resolutions and Tor computations (`KoszulResolution`), length comparison over a common residue field and along automorphisms (`FiniteLength`), geometric transitivity, sums of homology lengths and truncation of complexes over a local ring).
- `PerfectComplex/`: supported perfect complexes (`Basic`, homology support in `Support` and closure properties in `Closure`), their `K₀` (`K0`, including functoriality), normalized lengths (`NormalizedLength`) and the two Euler evaluations (`NormalizedEuler`, with the ordinary length as the special case `NormalizedLength.ordinary` in `OrdinaryEuler`), and generation of `K₀^{m}(A)` by the Koszul complex (`KoszulGeneration`).
- `Paper/`: the main statements (`Statement`), the explicit comparisons and supporting arguments of §5 (`Section5/`), and the paper's lemmas (`Corollary2_6`, `Lemma3_4`, `Lemma3_5` with `Ordinary`, `Normalized`, and `ConjugateSum`, `Lemma5_2`).
- `Inputs/`: theorems from outside the paper and standard facts not yet in Mathlib, stated with `sorry` or as classes (Theorem 2.5, Theorem 3.1, facts on regular local rings, the intersection-theory inputs of Lemma 5.2).
- `IntersectionMultiplicity/`: Serre's intersection multiplicity (`Basic`), normalized Tor lengths of finite-length modules (`NormalizedTor`, shared by Corollary 2.6 and Lemma 3.4), and the ingredients of Lemma 5.2 (rank factors of `χ`, base change of a finite free resolution, Euler evaluations of resolutions).

The general theorem `normalizedLength_tor_of_isWeaklyRegular`, its application in Lemma 3.4, Lemma 3.5b, 3.5c and Lemma 5.2 (`firstComparison`, modulo the general inputs of `Inputs/IntersectionTheory.lean`) are proved modulo the inputs; the remaining `sorry` declarations in the paper part are the positivity assertion of Corollary 2.6 (`cor_2_6_pos`) and the finiteness step of Lemma 3.5a for the normalized length (`lemma_3_5a_lam_finite`). See `notes/PLAN.md` §12–14.

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
- `notes/mathlib-review-2026-10-10.md` — Japanese documentation coverage, mathematical refactoring candidates, and comparison with the pinned Mathlib version
- `SerrePositivity/` — Lean sources

## Source and license

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
