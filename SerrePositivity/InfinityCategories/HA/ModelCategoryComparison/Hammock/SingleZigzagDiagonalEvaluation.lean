module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.SingleZigzagHomDiagram
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicialWeak

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial
variable (D : SimplexCategoryᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {O : Type w}
  (p : (i : SimplexCategoryᵒᵖ) → O → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : O),
    (D.map θ).functor.obj (p i X) = p j X)

def singleForwardDiagonalEvaluation (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.forwardHomDiagram D p hp X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardEvaluation D p hp X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.forwardHomDiagram D p hp X Y)).hom

lemma singleForwardDiagonalEvaluation_app (X Y : O) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y)).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardDiagonalEvaluation D p hp X Y).app n σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (σ.obj 0) := rfl

lemma singleForwardDiagonalEvaluation_weak (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardDiagonalEvaluation D p hp X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleForwardEvaluation D p hp X Y)
    (fun _ => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue_weak)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _)).isWeakHomotopyEquivalence

def singleBackwardDiagonalEvaluation (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.backwardHomDiagram D p hp X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardEvaluation D p hp X Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.backwardHomDiagram D p hp X Y)).hom

lemma singleBackwardDiagonalEvaluation_app (X Y : O) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.graphDiagram D p hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y)).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardDiagonalEvaluation D p hp X Y).app n σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)) := rfl

lemma singleBackwardDiagonalEvaluation_weak (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardDiagonalEvaluation D p hp X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.singleBackwardEvaluation D p hp X Y)
    (fun _ => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue_weak)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _)).isWeakHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram
