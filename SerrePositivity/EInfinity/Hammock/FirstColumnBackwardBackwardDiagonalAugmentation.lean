module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardDiagramIso
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardBackwardAugmentation
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordDiagonalAugmentation
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonalMap
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の後向き二列の対角 augmentation の厳密な正方形

概要：元の語の対角 augmentation と二方向全圏の対角比較射を同じ同型で照合する。
方針：全単体で元の相対関手と切断関手の正方形を使う。
規約：同じ比較射の弱同値性を移し、次数ごとの augmentation の弱同値性を仮定しない。
使われ方：DK5.7を既存の10.4–10.6へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory SimplicialLocalization SerrePositivity.InfinityCategories
variable (C : RelativeCategory.{u}) (w : Word) (X Y : C.category)
def backwardBackwardDiagonalTotalTargetIso :
    TwoSidedDiagram.diagonalTotalNerve ((Functor.const SimplexCategoryᵒᵖ).obj
      (backwardBackwardData C w X Y)) ≅ nerve (backwardBackwardTarget C.weakEquivalences w X Y) :=
  DoubleSimplicial.diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ
    (backwardBackwardData C w X Y) (TwoSidedDiagram.totalFunctor ⋙ nerveFunctor)) ≪≫
      DoubleSimplicial.diagonalConstantIso _

variable (D : SimplicialObject RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def backwardBackwardDiagonalAugmentation :
    TwoSidedDiagram.diagonalTotalNerve (backwardBackwardDiagram D p hp w X Y) ⟶
      nerve (backwardBackwardTarget C.weakEquivalences w X Y) :=
  TwoSidedDiagram.diagonalTotalMap (backwardBackwardAugmentation D C p hp A ha w X Y) ≫
    (backwardBackwardDiagonalTotalTargetIso C w X Y).hom

lemma backwardBackwardDiagonalAugmentation_square :
    (backwardBackwardDiagonalIso D p hp w X Y).hom ≫
      backwardBackwardDiagonalAugmentation C w X Y D p hp A ha =
    (FixedObjectDiagram.wordDiagonalAugmentation D C p hp A ha X Y).app
      (Word.append (Word.single .backward) (Word.cons .backward w)) ≫
        (backwardBackwardGraphIso C.weakEquivalences w X Y).hom := by
  ext n σ
  change σ ⋙ (backwardBackwardFunctor (D.obj n).weakEquivalences w (p n X) (p n Y) ⋙
    backwardBackwardRelativeFunctor w (A.app n) (ha n X) (ha n Y)) =
      σ ⋙ (Zigzag.Relative.fixedFunctor (A.app n) (ha n X) (ha n Y) ⋙
        backwardBackwardFunctor C.weakEquivalences w X Y)
  exact congrArg (fun H => σ ⋙ H)
    (backwardBackward_relative_functor w (A.app n) (ha n X) (ha n Y)).symm

lemma backwardBackwardDiagonalAugmentation_weak_iff :
    IsWeakHomotopyEquivalence ((FixedObjectDiagram.wordDiagonalAugmentation D C p hp A ha X Y).app
      (Word.append (Word.single .backward) (Word.cons .backward w))) ↔
    IsWeakHomotopyEquivalence (TwoSidedDiagram.diagonalTotalMap
      (backwardBackwardAugmentation D C p hp A ha w X Y)) := by
  have hS := (isPrecompositionEquivalence_of_iso
    (backwardBackwardDiagonalIso D p hp w X Y)).isWeakHomotopyEquivalence
  have hT := (isPrecompositionEquivalence_of_iso
    (backwardBackwardGraphIso C.weakEquivalences w X Y)).isWeakHomotopyEquivalence
  have hK := (isPrecompositionEquivalence_of_iso
    (backwardBackwardDiagonalTotalTargetIso C w X Y)).isWeakHomotopyEquivalence
  constructor
  · intro h
    have hc := h.comp hT
    rw [← backwardBackwardDiagonalAugmentation_square] at hc
    exact hK.cancel_right (hS.cancel_left hc)
  · intro h
    have hc := hS.comp (h.comp hK)
    change IsWeakHomotopyEquivalence ((backwardBackwardDiagonalIso D p hp w X Y).hom ≫
      backwardBackwardDiagonalAugmentation C w X Y D p hp A ha) at hc
    rw [backwardBackwardDiagonalAugmentation_square] at hc
    exact hT.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
