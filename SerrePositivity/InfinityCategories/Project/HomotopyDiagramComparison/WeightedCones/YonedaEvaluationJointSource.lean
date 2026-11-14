module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.YonedaEvaluationJointFibrations
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison

/-!
概要：元の共同 Yoneda 評価図式の C の対象への制限を、既存の全係数評価と照合する。
方針：元の同じ底への包含を使い、元の共同 Hom と共同評価の全写像を計算する。
規約：ここでは固定 C 対象の制限を証明。全 C の大域的な比較射は未構成。
使われ方：大域比較射の各 C 対象上の制限が、既存の Yoneda 比較と一致することの検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- C の元の対象を固定し、全前層係数を同じ共同底へ含める元の写像。 -/
def yonedaEvaluationJointSource {C : SSet.{u}} (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase C :=
  lift (SSet.const (ULift.up (SSet.opObjEquiv.symm y))) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C))

/-- 元の共同 Hom の底写像の制限は、元の Yoneda 像を始点とする同じ全包含。 -/
lemma yonedaHomJointBaseMap_source {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    yonedaEvaluationJointSource y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointBaseMap C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) :=
    by
  change lift (SSet.const (ULift.up (SSet.opObjEquiv.symm y)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} C).hom ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) = _
  rw [SSet.const_comp]
  rfl

/-- 元の全共同評価の同じ対象への制限は、元の前層評価そのもの。 -/
lemma yonedaEvaluationJointNative_source {C : SSet.{u}} (y : C _⦋0⦌) :
    yonedaEvaluationJointSource y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation y := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の共同 Hom 図式の同じ対象への制限は、元の全共変 Hom 関手。 -/
lemma yonedaHomJointDiagram_source {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaEvaluationJointSource y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointDiagram C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointDiagram, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    yonedaHomJointBaseMap_source]
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の共同評価図式の同じ対象への制限は、同じ元の評価の指定宇宙変更。 -/
lemma yonedaEvaluationJointDiagram_source {C : SSet.{u}} (y : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaEvaluationJointSource y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram C =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u} := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    yonedaEvaluationJointNative_source]

/-- 同じ対象に制限した元の共同図式は、元の全前層係数で自然同型。 -/
def yonedaEvaluationJoint_sourceIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaEvaluationJointSource y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointDiagram C)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaEvaluationJointSource y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram C) := by
  rw [yonedaHomJointDiagram_source, yonedaEvaluationJointDiagram_source]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso _ ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_evaluationIso y

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
