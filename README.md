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

`SerrePositivity/Paper/Section5/` contains the twisted Euler evaluations, the application of Lemma 3.5, and the final positivity argument. Lemma 5.2 (`firstComparison` in `Paper/Lemma5_2.lean`) takes its rings, finite algebras, ranks, parameters, group action, and length conditions as explicit arguments. The former `CoreData`, `IsPaperData`, and `Inputs.Core` bundles have been removed. `core_of_twistedEuler_pos` combines Lemma 5.2 with positivity of the twisted Euler values. `Section5.core_of_lengthAlgebras` derives these positive values from the supplied length algebras, and `core_of_normalization_bases` supplies the length algebras from the quoted Section 2 construction. Constructing the normalization bases and all remaining data from the core statement is still deferred. Ranks are written directly as `Module.finrank`.

Unproved inputs are explicit theorems, including `isWeaklyRegular_of_span_eq_maximalIdeal`,
`Inputs.intersectionVanishing`, and `Section2.theorem_2_5`. Their uses occur in proof bodies,
so downstream axiom audits expose `sorryAx`; there are no input classes to instantiate.
Do not introduce structures or classes to package theorem assumptions. State each needed
hypothesis directly. The former `Setup34`, `IsRegularNormalizationBase`, `LengthAlgebraProps`,
and `LengthAlgebraData` bundles have also been removed. Theorem 2.5 now explicitly quantifies
its output algebra and normalized length and lists its conclusions.
The domain property and bounded finite free resolution existence are proved from regular generators
of the maximal ideal. Only regularity of regular parameters remains an unproved regular-local input
(`Inputs/RegularParameters.lean`). The general resolution has length at most the number of generators.
Lemma 3.5a's normalized-length finiteness follows from the common finite-projective Koszul bounds
and the retract furnished by scalar null-homotopies. This proof uses no unproved inputs.
Lemmas 3.2 and 3.3 and their K-theory foundations remain deferred.
Section 2 (`Paper/Section2/`, 2026-10-10): the tower `Λ = lim A[t^{1/p^n}]`, its normalized length `λ_∞` (Faltings' three-step definition) and the Hilbert–Samuel multiplicity (leading coefficient of the Samuel polynomial, `CommutativeAlgebra/HilbertSamuel.lean`) are defined concretely rather than assumed. Lemma 2.4 and Corollary 2.6 (3) are proved from the sup property and the composition-series argument. The standard facts on the tower stages (monomial bases, free transition maps of rank `p^{(b−a)h}`, locality with residue field `k`, completeness, regularity, flatness of `Λ`; `Paper/Section2/MonomialBasis.lean`, `TowerStage.lean`) and the finite-stage formula and descent for `λ_∞` (`TowerDescent.lean`, with the base change of presented modules in `CommutativeAlgebra/PresentationBaseChange.lean`) are proved. Lemma 2.1, 2.2, Theorem 2.5 (now with the compatible `Λ`-action and `λ_D := λ_∞` by restriction of scalars), the two cited properties of `λ_∞` (`λ = λ*` on finitely generated modules and additivity, after Gabber–Ramero and Faltings), and the Hilbert–Samuel theorems (polynomiality, dimension, positivity) remain named `sorry`s. See `notes/section-2-plan.md`.
The current milestone is complete: the shared Euler, iterated-cone and symmetric-comparison theory,
its perfect-complex and rank-quotient realizations, and the connection from λ-flatness and λ-CM
conditions to the required Koszul inputs. Obsolete comparison layers and duplicated finiteness
and vanishing proofs have been removed; see `notes/cleanup-candidates-2026-10-11.md`.
Completing the cited descent results, the remaining Section 2 constructions, and the core/main
statements remains separate work.

The Lean sources are organized as follows (2026-10-11):

- `CategoryTheory/`: shared Euler additivity, homological evaluations, iterated cones, symmetric comparison, and triangulated K₀.
- `LengthAlgebra/`: length quotients, perfect-complex evaluations and comparison, vanishing and lower bounds, and the λ-flat/λ-CM input criteria.
- `Asymptotic/`: sequence categories, rank quotients, homological evaluations and their extension to the paper’s categories.
- `HomologicalAlgebra/`: general homological algebra over a ring (basic lemmas on complexes and finite free terms in `Basic`, mapping-cone long exact sequences in `ConeLES`, resolutions indexed by `ℤ` in `Resolution`, base change of complexes, `Tor` with resolution computations and annihilator actions, its long exact sequence, scalar null-homotopies (`NullHomotopy`), K-projective lifts).
- `CommutativeAlgebra/`: general commutative algebra (finite length, modules killed by a power of an ideal, finite local algebras, Hilbert–Samuel multiplicity, base change of presented modules (`PresentationBaseChange`), Koszul complexes and base change (`Koszul`), exactness, resolutions and Tor computations (`KoszulResolution`), length comparison over a common residue field and along automorphisms (`FiniteLength`), geometric transitivity, sums of homology lengths and truncation of complexes over a local ring).
- `PerfectComplex/`: supported perfect complexes (`Basic`, homology support in `Support` and closure properties in `Closure`), their `K₀` (`K0`, including functoriality), normalized lengths (`NormalizedLength`) and the two Euler evaluations (`NormalizedEuler`, with the ordinary length as the special case `NormalizedLength.ordinary` in `OrdinaryEuler`), and generation of `K₀^{m}(A)` by the Koszul complex (`KoszulGeneration`).
- `Paper/`: the main statements (`Statement`), the explicit comparisons and supporting arguments of §5 (`Section5/`), and the paper's lemmas (`Corollary2_6`, `Lemma3_4`, `Lemma3_5` with `Ordinary` and `Normalized`, `Lemma5_2`). The common conjugate-sum theorem is in `GroupTheory/ConjugateSum`.
- `Paper/Section2/`: §2 of the paper: the tower, its stages and their normalized length (`Tower`, `MonomialBasis`, `TowerStage`, `TowerLength`, `TowerDescent`), Lemma 2.1, 2.2, 2.4, Theorem 2.5 and Corollary 2.6 (3).
- `Inputs/`: theorems from outside the paper and standard facts not yet in Mathlib, stated as named theorems with `sorry` (Theorem 3.1, facts on regular local rings, the intersection-theory inputs of Lemma 5.2), and the rewriting of (2.4), (2.6) in terms of the base parameters (`LengthAlgebra`).
- `IntersectionMultiplicity/`: Serre's intersection multiplicity (`Basic`), normalized Tor lengths of finite-length modules (`NormalizedTor`, shared by Corollary 2.6 and Lemma 3.4), and the ingredients of Lemma 5.2 (rank factors of `χ`, base change of a finite free resolution, Euler evaluations of resolutions).

Every file has a Japanese module docstring (purpose, background, proof strategy, conventions, where it is used) and every declaration a Japanese docstring stating the claim in words, the role of its hypotheses and the idea of the proof; the conventions are recorded in `notes/PLAN.md` §18.

The general theorem `normalizedLength_tor_of_isWeaklyRegular`, its application in Lemma 3.4, Lemma 3.5b, 3.5c and Lemma 5.2 (`firstComparison`, modulo the general inputs of `Inputs/IntersectionTheory.lean`) are proved modulo the inputs; Lemma 3.5a, including `lemma_3_5a_lam_finite`, is proved without unproved inputs. Corollary 2.6 (`cor_2_6_pos`) is proved from `Section2.cor_2_6_residue_pos`, which depends on the positivity of the Hilbert–Samuel multiplicity. Direct `sorry` declarations in the paper part remain in the cited theorems of Section 2 and the core/main statements (`Paper/Statement.lean`). See `notes/PLAN.md` §11–12.

The Koszul Euler/rank identity now has an explicit derivation: the rank calculation for finite resolutions, the Koszul/Tor identification, and the general Euler–Poincaré formula for tensoring a finite free resolution are proved. The only remaining regular-local dependency is the named `sorry` theorem that regular parameters form a regular sequence. The domain property and finite free resolutions are now derived from it, using general theorems in `CommutativeAlgebra/RegularSequence.lean` and `HomologicalAlgebra/FiniteFreeResolution.lean`.

The plan has three layers:

1. **Paper-specific argument** (§5 and the formal parts of Lemma 3.4/3.5): to be formalized sorry-free first.
2. **New general theorems of the paper** (Theorem 3.1, rational K-theory descent; Theorem 4.7, asymptotic norm comparison): stated as named theorems with `sorry` at first, and checked by hand with priority.
3. **Inputs from the literature** (Serre, Roberts–Gillet–Soulé, Cohen–Gabber, Monsky, Roberts, Cai–Lee–Ma–Schwede–Tucker, Land–Tamme, Bhatt–Scholze): quoted as named theorems with `sorry`.

The first milestone is a sorry-free derivation of Theorem 1.1 in which `#print axioms` shows only the standard axioms once all required proofs are supplied; while quoted theorems remain unproved, dependent results explicitly carry `sorryAx`.

## Layout

- `paper/` — the preprint and its source (`SOURCE.md`)
- `notes/MEMO.md` — full investigation memo (in Japanese)
- `notes/PLAN.md` — current priorities, design conventions, dependency graph, interfaces, and links to the per-section notes (in Japanese)
- `notes/mathlib-review-2026-10-10.md` — comparison with the pinned Mathlib version and caveats on the scope of the formalization (in Japanese)
- `SerrePositivity/` — Lean sources

## Source and license

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
