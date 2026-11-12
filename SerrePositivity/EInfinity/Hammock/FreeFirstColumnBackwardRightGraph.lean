module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardRightDiagram

/-!
# 元の自由解像の右係数と残りの graph 図式

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
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeBackwardFirstTargetRightCategoryDiagramIso :
    rightDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ≅
    (Functor.const SimplexCategoryᵒᵖ).obj
      (Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag C.weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply Cat.Hom.ext
    change ((𝟭 _) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (W := C.weakEquivalences) (w := w) (Y := Y) (𝟙 Z)
      (C.weakEquivalences.id_mem Z)) ⋙
      (𝟭 _) = (𝟭 _) ⋙ (𝟭 _)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardFunctor_id, CategoryTheory.Functor.id_comp])

def freeBackwardFirstRightGraphDiagramIso :
    rightDiagram (D := freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ⋙ nerveFunctor ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change nerveFunctor.map ((rightDiagram (D := freeBackwardBackwardDiagram C w X Y)
      (freeFirstMarkedObjectEquiv C) (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z).map
        θ) ≫
        𝟙 _ = (𝟙 _) ≫ nerveFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram (freeResolution C)
          (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y).map θ)
    have he := (freeBackwardFirstRightCategoryDiagramIso C w X Y Z).hom.naturality θ
    change _ ≫ 𝟙 _ = (𝟙 _) ≫ _ at he
    have hh := congrArg nerveFunctor.map he
    simpa only [Category.comp_id, Category.id_comp] using hh)

def freeBackwardFirstTargetRightGraphDiagramIso :
    rightDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ⋙
        nerveFunctor ≅
    (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph C.weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change nerveFunctor.map ((rightDiagram
      (D := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y)
      (freeBackwardFirstTargetObjectEquiv_naturality C w X Y) Z).map θ) ≫
        𝟙 _ = (𝟙 _) ≫ 𝟙 _
    have he := (freeBackwardFirstTargetRightCategoryDiagramIso C w X Y Z).hom.naturality θ
    change _ ≫ 𝟙 _ = (𝟙 _) ≫ 𝟙 _ at he
    have hh := congrArg nerveFunctor.map he
    simpa only [Category.comp_id, Category.id_comp,
      CategoryTheory.Functor.map_id] using hh)

end SerrePositivity.EInfinity.Hammock.FirstColumn
