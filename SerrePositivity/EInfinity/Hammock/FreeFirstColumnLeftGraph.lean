module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnLeftDiagram

/-!
# 元の自由解像の左係数と残りの graph 図式

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
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.InfinityCategories
open Zigzag.FirstBoundary TwoSidedDiagram.FixedVertices
variable (C : RelativeCategory.{u}) (w : Word) (X Y Z : C.category)
def freeFirstTargetLeftCategoryDiagramIso :
    leftDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) Z ≅
    (Functor.const SimplexCategoryᵒᵖ).obj
      (Cat.of (Zigzag C.weakEquivalences (Word.cons .forward w) Z Y)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply Cat.Hom.ext
    change ((𝟭 _) ⋙ forwardFunctor (W := C.weakEquivalences) (w := w) (Y := Y) (𝟙 Z)) ⋙
      (𝟭 _) = (𝟭 _) ⋙ (𝟭 _)
    simp only [forwardFunctor_id, CategoryTheory.Functor.id_comp])

def freeFirstLeftGraphDiagramIso :
    leftDiagram (D := freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) Z ⋙ nerveFunctor ≅
    FixedObjectDiagram.graphDiagram (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) (Word.cons .forward w) Z Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change nerveFunctor.map ((leftDiagram (D := freeForwardForwardDiagram C w X Y)
      (freeFirstMarkedObjectEquiv C) (freeFirstMarkedObjectEquiv_naturality C w X Y) Z).map θ) ≫
        𝟙 _ = (𝟙 _) ≫ nerveFunctor.map ((FixedObjectDiagram.zigzagDiagram (freeResolution C)
          (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
          (Word.cons .forward w) Z Y).map θ)
    have he := (freeFirstLeftCategoryDiagramIso C w X Y Z).hom.naturality θ
    change _ ≫ 𝟙 _ = (𝟙 _) ≫ _ at he
    have hh := congrArg nerveFunctor.map he
    simpa only [Category.comp_id, Category.id_comp] using hh)

def freeFirstTargetLeftGraphDiagramIso :
    leftDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) Z ⋙
        nerveFunctor ≅
    (Functor.const SimplexCategoryᵒᵖ).obj (graph C.weakEquivalences (Word.cons .forward w) Z Y) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change nerveFunctor.map ((leftDiagram
      (D := (Functor.const SimplexCategoryᵒᵖ).obj (forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y)
      (freeFirstTargetObjectEquiv_naturality C w X Y) Z).map θ) ≫
        𝟙 _ = (𝟙 _) ≫ 𝟙 _
    have he := (freeFirstTargetLeftCategoryDiagramIso C w X Y Z).hom.naturality θ
    change _ ≫ 𝟙 _ = (𝟙 _) ≫ 𝟙 _ at he
    have hh := congrArg nerveFunctor.map he
    simpa only [Category.comp_id, Category.id_comp,
      CategoryTheory.Functor.map_id] using hh)

end SerrePositivity.EInfinity.Hammock.FirstColumn
