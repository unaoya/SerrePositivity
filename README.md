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

Statements (with `sorry` proofs) of Theorem 2.5 / Cor 2.6 (`Inputs/LengthAlgebra.lean`), Lemma 3.4 (`Descent/Lemma34.lean`) and Lemma 3.5 (`Descent/Lemma35.lean`) are in place, together with the definitions they need: Koszul complexes as iterated mapping cones (`Koszul.lean`), systems of parameters and Hilbert–Samuel multiplicity (`Multiplicity.lean`), perfect complexes supported at the closed point with their two Euler evaluations and twists (`Perfect.lean`), and geometric transitivity (`GeometricFiber.lean`). The current target is the proof of Lemma 3.4; see `notes/PLAN.md` §11. Done so far, with only the standard axioms: Koszul complexes of weakly regular sequences are resolutions (`KoszulExact.lean`), they give `ProjectiveResolution`s (`KoszulResolution.lean`), base change commutes with Koszul complexes (`KoszulBaseChange.lean`), and `Tor_i^A(A/(z), C) ≅ H_i(z; C)` (`TorKoszul.lean`). The abstract form of Lemma 3.4 (`lemma_3_4_of_isWeaklyRegular` in `Descent/Lemma34Abstract.lean`) is proved with only the standard axioms; this includes the long exact sequence of `Tor` (`Descent/TorLES.lean`, via mapping cones of lifts between projective resolutions) and the fact that `Tor` is killed by the annihilator (`Descent/TorTorsion.lean`). The paper's form (`Descent/Lemma34.lean`) and parts 1–2 of Cor 2.6 depend on two remaining `sorry`s, both standard facts about regular local rings (`Inputs/RegularLocalRing.lean`).

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
