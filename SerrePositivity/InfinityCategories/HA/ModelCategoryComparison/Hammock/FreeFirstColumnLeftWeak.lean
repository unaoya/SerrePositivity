module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeFirstColumnLeftGraph
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalForwardWeak

/-!
# 元の自由解像の左係数と残りの対角 augmentation の照合

概要：元の左係数の比較を残りの語の元の比較射自身へ戻す。
方針：元の全作用素を保つ同型と端点移送で同じ augmentation を回収する。
規約：残りの語の比較の弱同値性だけを帰納仮定として使う。
使われ方：DK5.7の元の全語の長さ帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeFirstLeftSpaceIso :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpace (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardForwardDiagram C w X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) Z Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftGraphDiagramIso C w X Y Z)
def freeFirstTargetLeftSpaceIso :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetObjectEquiv C w X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetObjectEquiv_naturality C w X Y) Z ≅
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph C.weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) Z Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetLeftGraphDiagramIso C w X Y Z) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso _
def freeFirstLeftSpaceMap :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.leftSpaceMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetObjectEquiv C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv_naturality C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetObjectEquiv_naturality C w X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardForwardAugmentation C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeFirstLeftSpaceIso_augmentation :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceIso C w X Y Z).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceMap C w X Y Z ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetLeftSpaceIso C w X Y Z).hom := by
  ext n σ
  have hZ : ((eqToHom (congrArg op
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv_augmentation C w X Y n Z))).unop).hom =
        eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z).symm := by
    rw [eqToHom_unop]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom (C := C) _
  change σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) =
    σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n) rfl
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor
        ((eqToHom (congrArg op
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv_augmentation C w X Y n Z))).unop).hom)
  rw [hZ, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardFunctor_eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z)]
  rfl
lemma freeFirstLeftSpaceMap_weak
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C Z Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceMap C w X Y Z) := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp h
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstLeftSpaceIso_augmentation] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstTargetLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
