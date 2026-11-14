module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaEvaluationClassification

/-!
概要：小さい前層を、持ち上げた同じ底上の一段大きい空間値前層へ送る。
方針：内部 Hom の標準宇宙同型、空間の指定宇宙変更、反転の宇宙同型を合成する。
規約：元の前層族の全写像を保持し、対象ごとの選択で関手を代用しない。
使われ方：P_Σ の左 Kan 延長の全自然 Hom 表示に必要な前層の宇宙変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の内部 Hom の標準宇宙比較は、同じ元の点での評価を厳密に保つ。 -/
lemma uliftInternalHomComparison_evaluation {A B : SSet.{u}} (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison.{u, v} A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up a) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) a) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ小さい前層族の値を、一段大きい空間として読む元の宇宙変更関手。 -/
def presheafUniverseDiagram (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison
      ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ≫
    (ihom _).map _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram ≫
      (pre ((SSet.uliftFunctor.{u + 2, u + 1}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} C).inv)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1}

/-- 元の前層の宇宙変更と評価は、同じ点の空間の宇宙変更へ厳密に可換。 -/
lemma presheafUniverseDiagram_evaluation (C : SSet.{u}) (c : C _⦋0⦌) :
    presheafUniverseDiagram C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation (ULift.up c) =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の宇宙変更は、底の同じ全射に沿う前層制限とも厳密に可換。 -/
lemma presheafUniverseDiagram_restriction {C D : SSet.{u}} (f : C ⟶ D) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction f) ≫
        presheafUniverseDiagram C =
      presheafUniverseDiagram D ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction ((SSet.uliftFunctor.{u + 1, u}).map f) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
