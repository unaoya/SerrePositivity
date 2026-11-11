module

public import SerrePositivity.EInfinity.Hammock.SingleZigzagHomDiagram
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak

/-!
# 元の単一列の対角から固定 Hom への弱比較

概要：元の graph の全作用素を保って対角を取る。
方針：元の自然変換と定数図式への標準同型を使う。
規約：元の比較射を保持する。
使われ方：DK5.7の元の自由解像の比較。
-/

@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory SerrePositivity.InfinityCategories DoubleSimplicial
variable (D : SimplexCategoryᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type w}
  (p : (i : SimplexCategoryᵒᵖ) → O → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : O),
    (D.map θ).functor.obj (p i X) = p j X)

def singleForwardDiagonalEvaluation (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y) ⟶
      forwardHomDiagram D p hp X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (singleForwardEvaluation D p hp X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (forwardHomDiagram D p hp X Y)).hom

lemma singleForwardDiagonalEvaluation_app (X Y : O) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y)).obj n) :
    (singleForwardDiagonalEvaluation D p hp X Y).app n σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (σ.obj 0) := rfl

lemma singleForwardDiagonalEvaluation_weak (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (singleForwardDiagonalEvaluation D p hp X Y) :=
  (diagonalFunctor_map_weak (singleForwardEvaluation D p hp X Y)
    (fun _ => ForwardZigzag.graphValue_weak)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _)).isWeakHomotopyEquivalence

def singleBackwardDiagonalEvaluation (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) ⟶
      backwardHomDiagram D p hp X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (singleBackwardEvaluation D p hp X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (backwardHomDiagram D p hp X Y)).hom

lemma singleBackwardDiagonalEvaluation_app (X Y : O) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y)).obj n) :
    (singleBackwardDiagonalEvaluation D p hp X Y).app n σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)) := rfl

lemma singleBackwardDiagonalEvaluation_weak (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (singleBackwardDiagonalEvaluation D p hp X Y) :=
  (diagonalFunctor_map_weak (singleBackwardEvaluation D p hp X Y)
    (fun _ => BackwardZigzag.graphValue_weak)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _)).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
