module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalQCatDiagramStrictification
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveCocartesianCoherentUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：有限順序の nerve 上で、同じ cocartesian 分類写像は本質的全射。
方針：任意の coherent 図式を局所 strict 化し、その weighted nerve の像と比較する。
規約：分類写像は元の全相対 Hom の作用で構成したものを保つ。
使われ方：Cat∞ 値分類の一般の底での局所存在と相対延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 有限順序の nerve 上の任意の Cat∞ 値図式は、strict な QCat 値図式で表せる。 -/
lemma exists_finiteQCatDiagramStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve A)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} n
  obtain ⟨A, ⟨h⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_localQCatDiagramStrictification (e.hom ≫ F)
  have h' := h.precomp e.inv
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'
  exact ⟨A, ⟨h'⟩⟩

/-- 任意の有限順序上の coherent 図式は、同じ分類写像による小さい weighted nerve の像と同型。 -/
lemma exists_cocartesianFiniteStraighteningVertexIso {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u},
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin (n + 1)))).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (A ⋙ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.qCatForget))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := by
  obtain ⟨A, ⟨h⟩⟩ := exists_finiteQCatDiagramStrictification F
  exact ⟨A, ⟨(_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedNerveCocartesianStraighteningVertexIso A).symm ≪≫ h.symm⟩⟩

/-- 有限順序の nerve 上の、構成済みの同じ cocartesian 分類写像は本質的全射。 -/
lemma cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin (n + 1)))) := by
  intro v
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).surjective v
  obtain ⟨A, h⟩ := exists_cocartesianFiniteStraighteningVertexIso F
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationInfinityVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (A ⋙ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.qCatForget)), h⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
