module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardRightGraph
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalBackwardWeak

/-!
# 元の自由解像の右係数と残りの対角 augmentation の照合

概要：元の右係数の比較を残りの語の元の比較射自身へ戻す。
方針：元の全作用素を保つ同型と端点移送で同じ augmentation を回収する。
規約：残りの語の比較の弱同値性だけを帰納仮定として使う。
使われ方：DK5.7の元の全語の長さ帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeBackwardFirstRightSpaceIso :
    rightSpace (freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (freeBackwardFirstRightGraphDiagramIso C w X Y Z)
def freeBackwardFirstTargetRightSpaceIso :
    rightSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ≅
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph C.weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (freeBackwardFirstTargetRightGraphDiagramIso C w X Y Z) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso _
def freeBackwardFirstRightSpaceMap :=
  rightSpaceMap (freeFirstMarkedObjectEquiv C) (freeBackwardFirstTargetObjectEquiv C w X Y)
    (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y)
    (freeBackwardFirstTargetObjectEquiv_naturality C w X Y) (freeBackwardBackwardAugmentation C w X
      Y)
    (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeBackwardFirstRightSpaceIso_augmentation :
    (freeBackwardFirstRightSpaceIso C w X Y Z).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) =
    freeBackwardFirstRightSpaceMap C w X Y Z ≫ (freeBackwardFirstTargetRightSpaceIso C w X Y Z).hom
      := by
  ext n σ
  have hZ : (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom =
        eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z)  :=
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom (C := C) _
  change σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) =
    σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n) rfl
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).property)
  simp only [hZ]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardFunctor_eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z)]
  rfl
lemma freeBackwardFirstRightSpaceMap_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeBackwardFirstRightSpaceMap C w X Y Z) := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeBackwardFirstRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp h
  rw [freeBackwardFirstRightSpaceIso_augmentation] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeBackwardFirstTargetRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
