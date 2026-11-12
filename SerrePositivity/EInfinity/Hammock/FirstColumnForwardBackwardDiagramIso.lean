module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardDiagram
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardCatIso
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardRelativeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonal

/-!
# 元の混合二方向の圏・graph 図式と対角の自然同型

概要：元の全相対作用素と両端の表示を保って比較を図式に束ねる。
方針：元の切断関手の全自然性と底・両係数の関手則を使う。
規約：元の全圏・graph と同じ augmentation を保持する。
使われ方：DK10.3・5.7の元の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v wO
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite
section Diagram
variable {I : Type v} [Category I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type wO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : O)

def forwardBackwardCategoryDiagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram D p hp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y ≅
      forwardBackwardDiagram D p hp w X Y ⋙ TwoSidedDiagram.totalFunctor :=
  NatIso.ofComponents
    (fun i => forwardBackwardCatIso (D.obj i).weakEquivalences w (p i X) (p i Y)) (by
      intro i j θ
      apply Cat.Hom.ext
      exact forwardBackward_relative_functor w (D.map θ) (hp θ X) (hp θ Y))

def forwardBackwardGraphDiagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y ≅
      forwardBackwardDiagram D p hp w X Y ⋙ TwoSidedDiagram.totalFunctor ⋙ nerveFunctor :=
  ((CategoryTheory.Functor.whiskeringRight (C := I) (D := Cat.{u, u})
    (E := SSet.{u})).obj nerveFunctor).mapIso (forwardBackwardCategoryDiagramIso D p hp w X Y)

lemma forwardBackwardGraphDiagramIso_hom_app (i : I) :
    (forwardBackwardGraphDiagramIso D p hp w X Y).hom.app i =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor (D.obj i).weakEquivalences w (p i X) (p i Y)) := rfl
end Diagram
section Diagonal
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type wO}
  (p : (i : SimplexCategoryᵒᵖ) → O → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : O),
    (D.map θ).functor.obj (p i X) = p j X) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : O)
def forwardBackwardDiagonalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y) ≅
    TwoSidedDiagram.diagonalTotalNerve (forwardBackwardDiagram D p hp w X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (forwardBackwardGraphDiagramIso D p hp w X Y)

lemma forwardBackwardDiagonalIso_hom_app (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y)).obj n) :
    (forwardBackwardDiagonalIso D p hp w X Y).hom.app n σ =
      σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardBackwardFunctor (D.obj n).weakEquivalences w (p n X) (p n Y) := rfl
end Diagonal
end SerrePositivity.EInfinity.Hammock.FirstColumn
