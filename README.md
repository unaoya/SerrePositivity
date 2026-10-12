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
its perfect-complex and rank-quotient realizations, and the connection to the main theorem
are implemented. The standard commutative algebra needed here is proved.

The formalization still depends on **13 external quotations and 2 deferred K-theory proofs**.
`main_statement` and `core_statement` have no direct `sorry`, but depend on `sorryAx`.
They are not proofs of the main theorem without those inputs.
The current input inventory and module map are maintained in [notes/status.md](notes/status.md).

## Reading order

1. [Japanese exposition](exposition/ja/exposition-ja.tex): shared theory (§3), length algebras (§4),
   perfect and rank realizations (§5–6), paper applications (§7), constructions (§8), core proof (§9).
   The [PDF](exposition/ja/exposition-ja.pdf) is generated from that TeX source.
2. [Section 4 interfaces](notes/section-4-plan.md) and [Section 2 implementation map](notes/section-2-plan.md).
3. [Current plan and conventions](notes/PLAN.md), then [historical records](notes/history/README.md).

## Layout

- `CategoryTheory/`: ring-independent Euler theory, iterated cones, comparison and triangulated K₀.
- `LengthAlgebra/`: length quotients, evaluations and concrete verification of the common hypotheses.
- `PerfectComplex/`: supported finite projective complexes and the older finite free model, with comparison APIs.
- `Asymptotic/`: sequence categories, rank quotients, localization and completed homological evaluations.
- `CommutativeAlgebra/`, `HomologicalAlgebra/`: proved general results, including regular parameters and resolutions.
- `Paper/`: constructions and applications to the paper, including the main statement.
- `Inputs/`: named external quotations, deferred descent, and explicitly marked compatibility imports.
- `paper/`: original preprint and source provenance.
- `notes/`: current interfaces, mathematical investigations and dated history.

New and changed APIs follow the Japanese documentation conventions in `notes/PLAN.md` §18.
This is a maintenance convention, not a claim that every existing declaration already satisfies it.
TeX is the source for explanatory PDFs; temporary compilation files and OS metadata are not retained.

## Verification

Run `lake build`, then `lake env lean scripts/audit_axioms.lean` and
`python3 scripts/check_documentation.py`. The axiom audit checks the shared APIs
and also reports the remaining dependencies of the main theorem.

## Source and license

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
