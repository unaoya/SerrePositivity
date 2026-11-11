module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportEnrichedDiagram
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningCoherent

/-!
概要：元の strict transport の豊穣図式の実現は、構成済みの同じ分類主写像。
方針：底と全 fibration の共同単体の各 Hom を、同じ section の混合作用へ戻す。
規約：対象の値だけでなく、主写像の全対象・全高次で厳密に一致する。
使われ方：底変換比較を同じ分類主写像の間の比較へ接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ底と全 fibration の対角評価は、元の section の混合作用による評価と一致する。 -/
lemma cocartesianStrictTransportEnrichedDiagram_diagonal
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramEvaluation A
      (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram C).toCoreEnrichedFunctor) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C) T := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom A
    (T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram C).toCoreEnrichedFunctor) i j).app n P =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsHom (A.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C) T i j).app n P
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramHom_of_le _ _ i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsHom_of_le _ _ i j hij]
  rfl

/-- 元の strict transport の豊穣図式の実現は、元の同じ Cat∞ 値分類主写像そのもの。 -/
lemma cocartesianStrictTransportEnrichedDiagram_realization (C : Type u) [Category.{u} C] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportEnrichedDiagram C).realization =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap C := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram.realization, uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryDiagramRealization, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact cocartesianStrictTransportEnrichedDiagram_diagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramSimplexBase σ.down) T

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
