module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnLeftGraph
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeWordDiagonalForwardWeak

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
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.InfinityCategories
open Zigzag.FirstBoundary TwoSidedDiagram.FixedVertices
variable (C : RelativeCategory.{u}) (w : Word) (X Y Z : C.category)
def freeFirstLeftSpaceIso :
    leftSpace (freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    DoubleSimplicial.diagonalFunctor.obj (FixedObjectDiagram.graphDiagram (freeResolution C)
      (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
      (Word.cons .forward w) Z Y) :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeFirstLeftGraphDiagramIso C w X Y Z)
def freeFirstTargetLeftSpaceIso :
    leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) Z ≅
        graph C.weakEquivalences (Word.cons .forward w) Z Y :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeFirstTargetLeftGraphDiagramIso C w X Y Z) ≪≫
    DoubleSimplicial.diagonalConstantIso _
def freeFirstLeftSpaceMap :=
  leftSpaceMap (freeFirstMarkedObjectEquiv C) (freeFirstTargetObjectEquiv C w X Y)
    (freeFirstMarkedObjectEquiv_naturality C w X Y)
    (freeFirstTargetObjectEquiv_naturality C w X Y) (freeForwardForwardAugmentation C w X Y)
    (freeFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeFirstLeftSpaceIso_augmentation :
    (freeFirstLeftSpaceIso C w X Y Z).hom ≫
      (freeWordDiagonalAugmentation C Z Y).app (Word.cons .forward w) =
    freeFirstLeftSpaceMap C w X Y Z ≫ (freeFirstTargetLeftSpaceIso C w X Y Z).hom := by
  ext n σ
  have hZ : ((eqToHom (congrArg op
      (freeFirstMarkedObjectEquiv_augmentation C w X Y n Z))).unop).hom =
        eqToHom (freeResolutionObject_augmentation C n Z).symm := by
    rw [eqToHom_unop]
    exact marked_eqToHom_hom (C := C) _
  change σ ⋙ Zigzag.Relative.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n Z) (freeResolutionObject_augmentation C n Y) =
    σ ⋙ (Zigzag.Relative.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n) rfl
      (freeResolutionObject_augmentation C n Y) ⋙ forwardFunctor
        ((eqToHom (congrArg op
          (freeFirstMarkedObjectEquiv_augmentation C w X Y n Z))).unop).hom)
  rw [hZ, forwardFunctor_eqToHom (freeResolutionObject_augmentation C n Z)]
  rfl
lemma freeFirstLeftSpaceMap_weak
    (h : IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (Word.cons .forward w))) :
    IsWeakHomotopyEquivalence (freeFirstLeftSpaceMap C w X Y Z) := by
  have hc := (isPrecompositionEquivalence_of_iso
    (freeFirstLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp h
  rw [freeFirstLeftSpaceIso_augmentation] at hc
  exact (isPrecompositionEquivalence_of_iso
    (freeFirstTargetLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
