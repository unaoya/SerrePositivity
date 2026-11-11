module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardDiagramIso
public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordDiagonalAugmentation
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonalMap
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の混合二方向 −+の対角 augmentation の厳密な正方形

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
open CategoryTheory SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
def backwardForwardDiagonalTotalTargetIso :
    TwoSidedDiagram.diagonalTotalNerve ((Functor.const SimplexCategoryᵒᵖ).obj
      (backwardForwardData C w X Y)) ≅ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardTarget C.weakEquivalences w X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ
    (backwardForwardData C w X Y) (TwoSidedDiagram.totalFunctor ⋙ nerveFunctor)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso _

variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def backwardForwardDiagonalAugmentation :
    TwoSidedDiagram.diagonalTotalNerve (backwardForwardDiagram D p hp w X Y) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardTarget C.weakEquivalences w X Y) :=
  TwoSidedDiagram.diagonalTotalMap (backwardForwardAugmentation D C p hp A ha w X Y) ≫
    (backwardForwardDiagonalTotalTargetIso C w X Y).hom

lemma backwardForwardDiagonalAugmentation_square :
    (backwardForwardDiagonalIso D p hp w X Y).hom ≫
      backwardForwardDiagonalAugmentation C w X Y D p hp A ha =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalAugmentation D C p hp A ha X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)) ≫
        (backwardForwardGraphIso C.weakEquivalences w X Y).hom := by
  ext n σ
  change σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor (D.obj n).weakEquivalences w (p n X) (p n Y) ⋙
    backwardForwardRelativeFunctor w (A.app n) (ha n X) (ha n Y)) =
      σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (A.app n) (ha n X) (ha n Y) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardForwardFunctor C.weakEquivalences w X Y)
  exact congrArg (fun H => σ ⋙ H)
    (backwardForward_relative_functor w (A.app n) (ha n X) (ha n Y)).symm

lemma backwardForwardDiagonalAugmentation_weak_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalAugmentation D C p hp A ha X Y).app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w))) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (TwoSidedDiagram.diagonalTotalMap
      (backwardForwardAugmentation D C p hp A ha w X Y)) := by
  have hS := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (backwardForwardDiagonalIso D p hp w X Y)).isWeakHomotopyEquivalence
  have hT := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (backwardForwardGraphIso C.weakEquivalences w X Y)).isWeakHomotopyEquivalence
  have hK := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (backwardForwardDiagonalTotalTargetIso C w X Y)).isWeakHomotopyEquivalence
  constructor
  · intro h
    have hc := h.comp hT
    rw [← backwardForwardDiagonalAugmentation_square] at hc
    exact hK.cancel_right (hS.cancel_left hc)
  · intro h
    have hc := hS.comp (h.comp hK)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((backwardForwardDiagonalIso D p hp w X Y).hom ≫
      backwardForwardDiagonalAugmentation C w X Y D p hp A ha) at hc
    rw [backwardForwardDiagonalAugmentation_square] at hc
    exact hT.cancel_right hc
end SerrePositivity.EInfinity.Hammock.FirstColumn
