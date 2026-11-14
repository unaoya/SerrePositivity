module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
/-!
概要：複体の短完全列で左項が非有界 acyclic なら、実右射影は準同型。
方針：実長完全列の隣接二項の零性から、全次数の Homology 射の単射性と全射性を得る。
規約：モデル圏は使わない。使われ方：分解 Hom の mapping cocone の実射影。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
/-- 左項が acyclic な短完全列の、同じ実右射影は全次数で準同型。 -/
lemma complexShortExact_quasiIso_projection {R : Type u} [CommRing R]
    (S : ShortComplex (Complex R)) (hS : S.ShortExact) (h₁ : S.X₁.Acyclic) :
    QuasiIso S.g := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz := (h₁ j).isZero_homology
  have hz' := (h₁ (j + 1)).isZero_homology
  have : Mono (homologyMap S.g j) :=
    (hS.homology_exact₂ j).mono_g (hz.eq_of_src _ _)
  have : Epi (homologyMap S.g j) :=
    (hS.homology_exact₃ j (j + 1) rfl).epi_f (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
