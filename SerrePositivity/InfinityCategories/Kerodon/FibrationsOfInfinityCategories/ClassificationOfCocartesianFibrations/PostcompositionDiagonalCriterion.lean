module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionDiagonalComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionHomCriterion

/-!
概要：元の一次元 Hom の同値性を、元の後合成と対角評価の同じ fiber 比較で判定する。
方針：検証済みの外ホーン判定を、同じ対角 fiber との厳密な同型で移す。
規約：同じ fiber 比較の同値性自体は未証明で、分類同値の完了とは主張しない。
使われ方：残る局所比較を二つの Kan fibration の fiber の比較へ接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionDiagonalCriterion

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFiber_kanComplex

local instance (b : ((SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalPostcompositionFiber F G b)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalPostcompositionFiber_kanComplex F G b
  infer_instance

/-- 同じ対角 fiber 比較の同値性は、元の外ホーン比較の同値性と必要十分。 -/
lemma cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalComparison F G b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionOuterHornComparison F G b) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalFiberIso F G b).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalFiberIso F G b)).isQCatEquivalence
  constructor
  · intro h
    have hh := h.comp hi
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalComparison_outerHorn] using hh
  · intro h
    apply hi.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalComparison_outerHorn]
    exact h

/-- 元の全 Hom 作用の同値性は、同じ全後合成・対角 fiber 比較の同値性と必要十分。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval F G) ↔
      ∀ b : ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPostcompositionDiagonalComparison F G b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionHomCriterion.cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_postcomposition]
  exact forall_congr' (fun b ↦
    (cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff F G b).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionDiagonalCriterion
