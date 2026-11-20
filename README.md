# SerrePositivity

Verification and Lean 4 formalization of the preprint
**Positivity of Serre's Intersection Multiplicity** (OpenAI, September 23, 2026),
which claims a proof of Serre's positivity conjecture for intersection multiplicities,
including the ramified mixed-characteristic case.

> **Theorem 1.1 (claimed).** Let (R, m) be a regular local ring and M, N nonzero finitely generated
> R-modules with ℓ(M ⊗ N) < ∞ and dim M + dim N = dim R. Then
> χ^R(M, N) = Σᵢ (−1)ⁱ ℓ(Tor_i^R(M, N)) > 0.

## Status

**The main theorem `SerrePositivity.main_statement` depends on exactly three unproved inputs** (checked by
the sorry-closure audit of `scripts/refactor/verify.sh`; `main_statement` itself has no direct `sorry`):

| Input | Meaning | Plan |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | the single Bhatt–Scholze quotation: the derived perfectoidization interface (BS *Prisms and prismatic cohomology*, Def 8.2, Lemma 8.4, Prop 8.5, Cor 8.11–8.12, 8.14, Thm 10.11) | goal A of [stage II](formalization-plans/stage-ii-plan-draft.md): build the original objects and fill every field |
| `theorem_3_1_K0` | Theorem 3.1 of the preprint (rational K-theory descent) at the level of K₀ | goal B: K-theory via Land–Tamme in dg-enhanced form |
| `Section4.supportedRankK0_descent` | the descent of Lemma 4.6 | goal B |

Everything else used by the main theorem is proved from the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

In the whole repository there are exactly four declarations containing `sorry`: the three above and one
off-path literature quotation, `InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillen_model_exists`
(existence of the Kan–Quillen model structure on simplicial sets, Hovey, *Model Categories*, Theorem 3.6.5).
It is outside the import closure of the root and outside the closure of the main theorem; 18 declarations
depend on it (the level model structure on circle spectra). The Mathlib pinned here has no `ModelCategory SSet`;
check again at each Mathlib bump whether the quotation can be replaced. No other axioms are used anywhere
(checked over all declarations of all modules by `research/cleanup-zero-base/whole/axioms_check.py`, 2026-11-20;
the allowed list is `research/cleanup-zero-base/whole/allowed.json`).

By section of the preprint:

- §2 (residue fields, normalized length, Theorem 2.5): proved relative to the E3 interface. The ring-level
  existence (Thm 1.17(1)) and excision (Cor 8.12) are derived from the interface; Thm 7.4, André's flatness
  lemma (Thm 7.14), Lemma 10.3, Prop 10.2, Remark 10.7 and the CLMST inputs (Prop 2.4.7, Cor 4.0.4) are proved.
  Cohen and Cohen–Gabber normalization, the complete flat residue-field extension and the completed root tower
  are constructed without quotations.
- §3 (Lemmas 3.4–3.5): proved, except Theorem 3.1.
- §4 (Theorem 4.7): proved, except the descent of Lemma 4.6.
- §5 (Lemmas 5.1–5.6, the reduction and the core case): proved, including the Roberts–Gillet–Soulé vanishing
  (supported cyclic Adams operations) and the residue-characteristic-zero case (Serre's diagonal argument).

### What is formalized (2026-11-05)

About 31,000 Lean files and 2.7 million lines under `SerrePositivity/` (plus 1,800 archived files that are tracked but not built).

| Area | Files / lines | Content |
| --- | ---: | --- |
| The paper (`Paper/`, `IntersectionMultiplicity/`, `LengthAlgebra/`, `Asymptotic/`, `KTheory/`, `PerfectComplex/`, `CategoryTheory/`) | ~210 / 62k | Euler theory, iterated cones, length algebras, perfect-complex and rank-quotient realizations, the four sections of the preprint and the main statement |
| Commutative and homological algebra (`CommutativeAlgebra/`, `HomologicalAlgebra/`, `FieldTheory/`, …) | ~520 / 103k | regular local rings, Koszul complexes, Hilbert–Samuel multiplicity, Tor, minimal resolutions, derived completion, Cohen structure theory, perfection and perfectoid rings, universal homeomorphisms and the étale stratification of finite maps (BS Lemma 10.12) |
| Bhatt–Scholze (`BhattScholze/`, `CLMST/`) | ~160 / 113k | δ-rings, prisms, perfectoid ideals, almost mathematics, André's lemma, perfectoidization and its ring-level consequences, the CLMST arguments |
| ∞-categories (`InfinityCategories/`) | ~14,700 / 1.12M | quasicategories (join, slice, limits, mapping spaces, Joyal), Kan complexes, coherent nerve, straightening, Yoneda, Kan extensions, adjunctions, cofinality, localization, homotopy limits (Bousfield–Kan), stable ∞-categories and Verdier sequences, Cat∞, Ind, accessible and presentable ∞-categories, the adjoint functor theorem (HTT 5.5.2.9), Bousfield localization, the dg nerve, D(A) = N_dg(semifree A-modules) with its stability and presentability, Verdier fractions, dg gluing, the derived tensor ∞-functor |
| dg categories (`DifferentialGraded/`) | ~470 / 150k | dg categories, modules, complexes, derived functors, perfect and compact objects, dg quotients |
| E∞-algebras (`EInfinity/`) | ~2,600 / 201k | Barratt–Eccles operad, E∞-dg algebras, transferred model structure, CAlg as a coherent nerve, Alexander–Whitney and shuffle maps |
| Homotopical algebra and spectra (`HomotopicalAlgebra/`, `Spectra/`) | ~1,370 / 130k | model categories (kept outside the ∞-categorical core), simplicial homotopy theory, symmetric spectra |
| K-theory (`KST/`) | ~9,200 / 715k | localizing invariants, S• construction, fibration theorem, non-connective K, comparison, derived blow-ups, derived geometry, pro-excision, scheme lemmas (the K-specific parts; general parts were moved into `InfinityCategories/`) |

The layering of the ∞-categorical core is checked mechanically (`scripts/refactor/layer_check.py`): the core layers
`Simplicial < Core < Kan < Coherent < {F1, F1B, HomotopyLimits} < Stable < F2 < StablePresentable` import only lower
layers, and no KST, dg or E∞ code (one remaining model-category dependency, item M16 of the plan).

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
5. [`formalization-plans/`](formalization-plans/): the [stage II plan](formalization-plans/stage-ii-plan-draft.md),
   the [coordination rules](formalization-plans/coordination.md) and the plans of each area.

## Layout

- `Paper/`, `IntersectionMultiplicity/`: the preprint's constructions and the main statement.
- `CategoryTheory/`, `LengthAlgebra/`, `PerfectComplex/`, `Asymptotic/`, `KTheory/`: ring-independent Euler theory, length algebras and the two realizations.
- `CommutativeAlgebra/`, `HomologicalAlgebra/`, `FieldTheory/`, `RingTheory/`, `LinearAlgebra/`, `GroupTheory/`: proved general results.
- `BhattScholze/`, `CLMST/`: the perfectoid side; `BhattScholze/Inputs/` holds the single quotation (E3).
- `InfinityCategories/`: the ∞-categorical foundations (map in `InfinityCategories/README.md`).
- `DifferentialGraded/`, `EInfinity/`, `HomotopicalAlgebra/`, `Spectra/`, `KST/`: dg categories, E∞-algebras, model categories and spectra, K-theory.
- `Inputs/`: the two deferred K-theory statements and compatibility entries.
- `Archive/`: tracked but not built (superseded developments).
- `formalization-plans/`: plans, instructions and lane reports (index at the top of its README); `archive/` holds finished plans, `archive/stage-i/` the stage I plans, `archive/reports/` the finished stages of lane reports.
- `research/`, `blueprint/`, `exposition/`, `evidence/`, `paper/`: see **Documents** below; the preprints.
- `scripts/`: audits (`scripts/audit/`, `scripts/audit_*.lean`) and the refactoring tools (`scripts/refactor/`).

## Conventions

- **Quotations and deferred proofs.** Each external result is a named `sorry` theorem whose
  docstring states the source and the scope of what is quoted, applied directly where it is used.
  The two deferred K-theory statements are kept apart from the quotations. Completion is judged
  with `#print axioms` and `#print sorries`, not by the absence of a direct `sorry`.
- **Citations in docstrings (2026-11-12).** Docstrings cite the source by its own numbering
  (for example "BS 著者版 Lemma 2.15", "HTT 5.5.2.9", a Kerodon or Stacks tag). They do not cite the
  study notes (`exposition/`), their numbering, task labels (T2-n) or refactor labels (BR, R); the
  notes cite Lean, not the other way. Refactor candidates live in `formalization-plans/refactor-ledger.md`.
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
  Since 2026-11-19 (cleanup): auxiliary declarations may carry a one-line docstring; the full form
  is for declarations matching an item of the literature and for the main definitions. Lines are
  at most 100 characters.

## Mathlib and in-repository foundations

The pinned Mathlib (`lake-manifest.json`) supplies `Module.length` and its additivity
(`Module.length_eq_add_of_exact`), left derived functors (`CategoryTheory.Tor`; the comparison with
`Tor'` is not in Mathlib), extension of scalars, regular local rings, Krull dimension and supports.
Koszul complexes, Hilbert–Samuel multiplicity, the Tor long exact sequence and symmetry, minimal
free resolutions and the length-based Euler characteristics are built here (`CommutativeAlgebra/`,
`HomologicalAlgebra/`).

## Remaining work

Stage I (reorganizing the foundations, 2026-10-31 to 11-05) is complete. Stage II removes the three inputs; its plan
is [formalization-plans/stage-ii-plan-draft.md](formalization-plans/stage-ii-plan-draft.md) (a draft to be finalized):

- **Goal A (Bhatt–Scholze):** the design A0–A9 and Lean skeletons are in `formalization-plans/bhatt-scholze/drafts/`
  (51 files); they are moved into the library while their `sorry`s are proved, on top of ∞-sheaf theory (S1–S8) and
  ∞-categorical inputs (presentability, tensoring with spaces, E∞-algebras). Three classical results (a crystalline
  comparison, BS17 Thm 4.1, BM18 Thm 1.7) remain permanent quotations.
- **Goal B (K-theory):** Verdier quotients and localization in the ∞-categorical core (M1–M11), then K-theory of
  small stable ∞-categories (Cat^perf, S•, non-connective K, localizing invariants), Tamme's splitting and the
  Land–Tamme theorem, the scheme-theoretic axioms and the descent of Theorem 3.1 and Lemma 4.6.
- Smaller items: extending the Koszul multiplicity formula to finite modules; restating Lemma 5.4 over an abstract
  tower-compatible length.

## Documents

Human-readable text lives in four places. Each may cite only what is listed (rule of 2026-11-17; the
earlier note is in `formalization-plans/doc-reorg/README.md`):

| Place | Role | May cite | Cited by |
| --- | --- | --- | --- |
| Lean docstrings | the claim, the source numbering (HTT 5.5.2.9, a Kerodon tag, "BS Lemma 2.15"), proof idea, use sites | the literature only | everything |
| `research/` | the data: coverage tables per source (`*-coverage/review*.csv`), item closures (`p0-lurie/`), map pages (`*/map/`), audits | the literature and Lean | `blueprint/`, `exposition/`, `formalization-plans/` |
| `blueprint/` | the generated human-readable account (Verso Blueprint): chapters per source, nodes bound to Lean declarations; later also the essays | generated from `research/` and Lean; hand-written facts are not kept here | `exposition/` (until unified), `formalization-plans/` |
| `exposition/` | the older Japanese expositions; **frozen since 2026-11-17**, to be absorbed into `blueprint/` (see `exposition/README.md` for the classification) | the literature, Lean, `blueprint/` | `formalization-plans/` |
| `formalization-plans/` | plans, instructions, lane reports, decisions, ledgers | anything | nothing: no other place relies on a plan for a fact |

Verification evidence (collections, logs, comparison outputs) is not a document; existing files are under
`evidence/`, new ones stay outside git with a manifest committed (`evidence/README.md`).

## Generated files

TeX is the source of the exposition and of the research notes; the PDF next to each source is the
generated viewing copy. After changing a TeX file, regenerate with
`latexmk -lualatex -outdir=<temporary directory> <source>`, check warnings, cross-references and the
changed pages, then update the PDF. Logs, auxiliary files and page images are not tracked, nor is
OS metadata. `paper/paper.pdf` and `paper/lech.pdf` are kept as the sources of the claims.

## Verification

`zsh scripts/refactor/verify.sh` builds the root and all audit targets, runs every audit (about 100) and the
sorry-closure audit of the main theorem; it reports `gate: true` when everything passes
(`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40` are the defaults). The Lake artifact cache can be shared between
worktrees (`LAKE_ARTIFACT_CACHE=true`, `LAKE_RESTORE_ARTIFACTS=true`). `python3 scripts/check_documentation.py`
checks local links and the Lean names referenced in the expositions.

## Source and license

Copyright (c) 2026 Naoya Umezaki.
The Lean code, scripts and documentation in this repository are licensed under the
Apache License, Version 2.0; see `LICENSE`.

The preprint is taken from [openai/math](https://github.com/openai/math)
(commit `adc7f1241b42`, family 193), distributed under the Apache License 2.0.
See `paper/SOURCE.md`. This project is not affiliated with OpenAI.
Reference papers used for checking citations (`paper/refs/`) are not distributed with this
repository.
