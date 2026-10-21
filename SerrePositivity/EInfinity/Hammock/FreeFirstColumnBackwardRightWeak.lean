module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardRightGraph
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeWordDiagonalBackwardWeak

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
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.InfinityCategories
open Zigzag.FirstBoundary TwoSidedDiagram.FixedVertices
variable (C : RelativeCategory.{u}) (w : Word) (X Y Z : C.category)
def freeBackwardFirstRightSpaceIso :
    rightSpace (freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    DoubleSimplicial.diagonalFunctor.obj (FixedObjectDiagram.graphDiagram (freeResolution C)
      (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X)
      (Word.cons .backward w) Z Y) :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeBackwardFirstRightGraphDiagramIso C w X Y Z)
def freeBackwardFirstTargetRightSpaceIso :
    rightSpace ((Functor.const SimplexCategoryᵒᵖ).obj (backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ≅
        graph C.weakEquivalences (Word.cons .backward w) Z Y :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeBackwardFirstTargetRightGraphDiagramIso C w X Y Z) ≪≫
    DoubleSimplicial.diagonalConstantIso _
def freeBackwardFirstRightSpaceMap :=
  rightSpaceMap (freeFirstMarkedObjectEquiv C) (freeBackwardFirstTargetObjectEquiv C w X Y)
    (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y)
    (freeBackwardFirstTargetObjectEquiv_naturality C w X Y) (freeBackwardBackwardAugmentation C w X
      Y)
    (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeBackwardFirstRightSpaceIso_augmentation :
    (freeBackwardFirstRightSpaceIso C w X Y Z).hom ≫
      (freeWordDiagonalAugmentation C Z Y).app (Word.cons .backward w) =
    freeBackwardFirstRightSpaceMap C w X Y Z ≫ (freeBackwardFirstTargetRightSpaceIso C w X Y Z).hom
      := by
  ext n σ
  have hZ : (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom =
        eqToHom (freeResolutionObject_augmentation C n Z)  :=
    marked_eqToHom_hom (C := C) _
  change σ ⋙ Zigzag.Relative.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n Z) (freeResolutionObject_augmentation C n Y) =
    σ ⋙ (Zigzag.Relative.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n) rfl
      (freeResolutionObject_augmentation C n Y) ⋙ backwardFunctor
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z)).property)
  simp only [hZ]
  rw [backwardFunctor_eqToHom (freeResolutionObject_augmentation C n Z)]
  rfl
lemma freeBackwardFirstRightSpaceMap_weak
    (h : IsWeakHomotopyEquivalence
      ((freeWordDiagonalAugmentation C Z Y).app (Word.cons .backward w))) :
    IsWeakHomotopyEquivalence (freeBackwardFirstRightSpaceMap C w X Y Z) := by
  have hc := (isPrecompositionEquivalence_of_iso
    (freeBackwardFirstRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp h
  rw [freeBackwardFirstRightSpaceIso_augmentation] at hc
  exact (isPrecompositionEquivalence_of_iso
    (freeBackwardFirstTargetRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
