# SerrePositivity

Verification and Lean 4 formalization of the preprint
**Positivity of Serre's Intersection Multiplicity** (OpenAI, September 23, 2026),
which claims a proof of Serre's positivity conjecture for intersection multiplicities,
including the ramified mixed-characteristic case.

> **Theorem 1.1 (claimed).** Let (R, m) be a regular local ring and M, N nonzero finitely generated
> R-modules with ℓ(M ⊗ N) < ∞ and dim M + dim N = dim R. Then
> χ^R(M, N) = Σᵢ (−1)ⁱ ℓ(Tor_i^R(M, N)) > 0.

## Status

The shared Euler, iterated-cone, vanishing, lower-bound and symmetric-comparison theory,
its perfect-complex and rank-quotient realizations, the standard commutative algebra used
(regular parameters, unmixedness, Hilbert–Samuel theory, the Koszul multiplicity formula) and
the connection to the main theorem are implemented.

The main theorem still depends on **1 external quotation (the Bhatt–Scholze perfectoidization interface) and 2 deferred K-theory proofs**.
`main_statement` and `core_statement` have no direct `sorry`, but depend on `sorryAx`.
They are not proofs of the main theorem without those inputs. The complete Noetherian flat
residue-field extension is now constructed without quotations; its legacy `Inputs` entry point
and Lemma 2.1 depend only on the standard axioms. Mixed-characteristic Cohen normalization
with perfect residue field is also constructed without quotations, including the Witt coefficient
map, parameters, finite power-series evaluation and injectivity. Equal-characteristic Cohen–Gabber
normalization is now proved for arbitrary residue fields by changing the coefficient section,
constructing a differential parameter basis and proving separability for the same finite injective
power-series evaluation. Its legacy entry point and Lemma 2.2 use only the standard axioms
(see Lemma 2.2 in [the Japanese exposition](exposition/ja/exposition-ja.tex)).
The standard completed root tower
is now proved integral perfectoid via finite-stage Frobenius kernels and the actual tilt and Fontaine
kernel. Roberts' Frobenius homology vanishing is no longer used: the equal-characteristic
construction only needs it for Koszul complexes on a system of parameters, which is proved
elementarily in `CommutativeAlgebra/ParameterKoszulGrowth.lean` (a uniform annihilator of Tor over
a power series ring and a fixed finite free resolution give `ℓ H_i(z^q; D) = O(q^{h-1})`;
see the remark `rem:koszul-elementary` in [the exposition](exposition/ja/exposition-ja.tex)). Serre's equal-characteristic
positivity is no longer used either: the residue-characteristic-zero case needed by the main
theorem is proved by Serre's reduction to the diagonal in
`IntersectionMultiplicity/EqualCharZeroPositivity.lean`, using a local flatness criterion
(`HomologicalAlgebra/LocalFlatnessCriterion.lean`), the coefficient field in characteristic zero
and a comparison of Tor over `R` and over `R[[Y]]`
(see appendix A of [the exposition](exposition/ja/exposition-ja.tex)). By section of the preprint:

- §2 (residue fields, normalized length, Theorem 2.5): proved relative to the existence of
  the derived perfectoidization interface from Bhatt–Scholze, *Prisms and prismatic cohomology*
  (`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`). The ring-level existence theorem
  (Thm 1.17(1), `BhattScholze.Inputs.exists_perfectoidization_of_integral`) and excision theorem
  (Cor 8.12, `BhattScholze.Inputs.perfectoidization_excision_isPullback`) are now derived from
  that interface, preserving their public types. The difference map is also proved surjective.
  The surjectivity Thm 7.4, André's flatness lemma Thm 7.14, Lemma 10.3, Prop 10.2 and
  Remark 10.7 are proved in the repository. CLMST Proposition 2.4.7 and Corollary 4.0.4
  retain their existing entry points and depend on the single interface quotation
  (see appendix A of the exposition for its scope).
- §3 (Lemmas 3.4–3.5): proved, except that Theorem 3.1 (rational K-theory descent) is deferred
  (`theorem_3_1_K0`).
- §4 (Theorem 4.7): proved, except that the descent of Lemma 4.6 is deferred
  (`Section4.supportedRankK0_descent`).
- §5 (Lemmas 5.2–5.6, the reduction and the core case): proved. The Roberts–Gillet–Soulé
  vanishing theorem (`Inputs.intersectionVanishing`) is proved in all residue characteristics
  using supported cyclic Adams operations (the square, and the cube after a cyclotomic local
  extension in residue characteristic two). The residue-characteristic-zero case (Lemma 5.1)
  is proved by Serre's diagonal argument; the former general quotation
  `Inputs.serrePositivity_of_field` has been removed.

The cyclic length estimate used in CLMST Proposition 4.0.10 is proved from finite-stage
Frobenius bounds and low-dimensional length growth, with the Bhatt–Scholze existence
(Cor 7.3) and surjectivity (Thm 7.4), both proved here. The all-stage parameter quotient
formula (Proposition 4.0.14) is proved from the shared Euler and cone theory, flat base change
and finite-stage length calculations. CLMST Proposition 2.4.7 (the cone of `S → S_perfd` is a
`J`-isogeny) and Corollary 4.0.4 (almost vanishing of local cohomology and Koszul homology of
`C_D`) are now proved following the CLMST arguments: base change along a proved André extension,
Zariski-local splitting of finite étale algebras over absolutely integrally closed rings, the
ring excision theorem derived from the interface for the kernel and cokernel bounds, the elementary Claim 2.4.8, and
descent along `p`-completely faithfully flat maps; the Tor input of Theorem 4.0.3(a) is proved for
all modules by the Milnor sequence and Prop 10.2. The idempotence of the perfectoid ideal modulo
`p` powers (Remark 10.7) is proved from Lemma 10.3 and Thm 7.4; neither is a quotation any more.

The three legacy CLMST entry points in `Inputs/CLMST.lean` are proved compatibility
wrappers around the Paper-independent CLMST layer. Current boundaries and subsequent
review tasks are recorded in [the CLMST plan](formalization-plans/clmst.md).

The table of quotations, the status of every proposition and the module map are kept in
appendix A of the exposition; the actual dependencies are checked by `scripts/audit_axioms.lean`.

## Reading order

1. [Japanese exposition](exposition/ja/exposition-ja.tex) (the [PDF](exposition/ja/exposition-ja.pdf)
   is generated from it): §3 shared theory, §4 length algebras, §5–6 the two realizations,
   §7 applications to the paper, §8 constructions, §9 core proof. Appendix A lists the
   quotations, the status and the implementation map; appendices B–D discuss related work,
   intuition and a λ-flat reformulation. Each statement ends with the Lean declaration it
   corresponds to.
2. The module docstrings, which follow the numbering of the paper and of the exposition.
3. [`research/`](research/): independent research notes (λ-étale extensions, λ-homological
   algebra). They contain conjectural material and are not used for the status of the main theorem.
4. [Exposition of *Lech's multiplicity conjecture*](exposition/ja/lech-ja.tex) (the
   [PDF](exposition/ja/lech-ja.pdf) is generated from it), the companion preprint
   [`paper/lech.pdf`](paper/lech.pdf), which uses the same length-algebra method. It is not
   formalized yet.
5. [`formalization-plans/`](formalization-plans/): plans for the remaining formalization
   (external quotations, K-theory, CLMST, Frobenius homology, Lech's conjecture).

## Layout

- `CategoryTheory/`: ring-independent Euler theory, iterated cones, comparison and triangulated K₀.
- `LengthAlgebra/`: length quotients, evaluations and concrete verification of the common hypotheses.
- `PerfectComplex/`: supported finite projective complexes and the older finite free model, with comparison APIs.
- `Asymptotic/`: sequence categories, rank quotients, localization and completed homological evaluations.
- `CommutativeAlgebra/`, `HomologicalAlgebra/`: proved general results, including regular parameters, resolutions, finite-generation agreement for normalized length,
  almost module categories and principal derived completeness.
- `Paper/`: constructions and applications to the paper, including the main statement.
- `Inputs/`: named external quotations, deferred descent, and explicitly marked compatibility imports.
- `paper/`: original preprint, the Lech preprint and source provenance (`paper/refs/` holds
  local copies of cited papers and is not tracked).
- `formalization-plans/`: plans for the remaining formalization (Markdown).
- `research/`: independent research notes (TeX sources with generated PDFs, and Markdown).
- `scripts/`: the axiom audit and the documentation check.

## Conventions

- **Quotations and deferred proofs.** Each external result is a named `sorry` theorem whose
  docstring states the source and the scope of what is quoted, applied directly where it is used.
  The two deferred K-theory statements are kept apart from the quotations. Completion is judged
  with `#print axioms` and `#print sorries`, not by the absence of a direct `sorry`.
- **No hypothesis bundles.** No structure or class whose fields are unproved statements
  (`Setup34`, `LengthAlgebraProps`, `LengthAlgebraData` are not to be reintroduced). Mathematical
  structures (`NormalizedLength`, categories, functors, resolutions) carry their laws, and
  existence theorems quantify over actual objects.
- **Direction of dependencies.** `CategoryTheory/` is independent of rings, towers and the paper.
  The realizations verify support, finiteness, amplitude, shifts and group actions. Proved general
  results live in `CommutativeAlgebra/` and `HomologicalAlgebra/`; `Inputs/` keeps only quotations
  and compatibility entries.
- **Tor, twists, universes.** Mathlib's `CategoryTheory.Tor` is derived in the second variable;
  `TorAlg φ i V` resolves `V` and is read as `Tor_i^A(C, V)`. The higher naturality of the exchange
  isomorphism is a separate claim and is not inferred from the linear equivalence. On the old K₀ the
  left action is `g • [P] = [twist g⁻¹ P]`, and reindexing of group sums is explicit. Rings and
  modules live in `ModuleCat.{u}`.
- **Numerical values.** `ENat.toNat`, `ENNReal.toReal` and `finsum` send infinite values to zero.
  Definitional identities are distinguished from additivity, which is only claimed after
  finiteness is established. Conversions of ordinary lengths go through `FiniteLengthValue`; cones
  and alternating sums use the shared categorical API.
- **Multiplicity.** Defined as the leading coefficient of the Samuel polynomial; (2.5) is stated
  as in the paper. The Koszul multiplicity formula is proved for the ring itself; its extension to
  arbitrary finite modules is a separate task and is not hidden in the hypotheses of the current
  theorems.
- **Docstrings.** New and changed declarations have Japanese docstrings stating the claim, the
  role of the hypotheses, the proof idea and the use sites; mathematical structures document their
  laws and meaning; short compatibility entries name their replacement. This is a maintenance
  convention, not a claim that every existing declaration already satisfies it.

## Mathlib and in-repository foundations

The pinned Mathlib (`lake-manifest.json`) supplies `Module.length` and its additivity
(`Module.length_eq_add_of_exact`), left derived functors (`CategoryTheory.Tor`; the comparison with
`Tor'` is not in Mathlib), extension of scalars, regular local rings, Krull dimension and supports.
Koszul complexes, Hilbert–Samuel multiplicity, the Tor long exact sequence and symmetry, minimal
free resolutions and the length-based Euler characteristics are built here (`CommutativeAlgebra/`,
`HomologicalAlgebra/`).

## Remaining work

- The two deferred descent proofs: Theorem 3.1 at the level of K₀, and Lemma 4.6 together with
  descent for general coefficients.
- Restating the finite approximation (Lemma 5.4) over an abstract tower-compatible length, as in
  exposition §4.5, instead of the concrete tower.
- Extending the Koszul multiplicity formula from the ring to arbitrary finite modules (Rees
  evaluation, boundary lifting, Samuel degree of the support).
- The 2 Bhatt–Scholze quotations remain quotations: Thm 1.17(1) (its proof needs derived
  prismatic cohomology and arc descent) and the ring-level consequence of Cor 8.12 (its proof needs
  arc descent of perfectoidizations). The legacy quotations of Serre's equal-characteristic
  positivity and of Roberts' Frobenius vanishing have been deleted; the remaining off-path
  quotation `Inputs.Homotopy.kanQuillen_model_exists` belongs to the K-theory development.

## Documents and generated files

TeX is the source of the exposition and of the research notes; the PDF next to each source is the
generated viewing copy. After changing a TeX file, regenerate with
`latexmk -lualatex -outdir=<temporary directory> <source>`, check warnings, cross-references and the
changed pages, then update the PDF. Logs, auxiliary files and page images are not tracked, nor is
OS metadata. `paper/paper.pdf` and `paper/lech.pdf` are kept as the sources of the claims.

## Verification

Run `lake build`, then `lake env lean scripts/audit_axioms.lean` and
`python3 scripts/check_documentation.py`. The axiom audit checks the shared APIs and reports the
remaining dependencies of the main theorem; the documentation check verifies the local links of
the README, the research notes and the formalization plans, and every Lean name referenced in
the two expositions.

## Source and license

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
