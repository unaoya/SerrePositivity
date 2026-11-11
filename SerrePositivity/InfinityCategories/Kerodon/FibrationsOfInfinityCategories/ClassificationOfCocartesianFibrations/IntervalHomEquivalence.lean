module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionComparisonEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionDiagonalCriterion

/-!
概要：実際の輸送図式の一次元 Hom の元の作用は同値。
方針：元の後合成 fiber 比較と標準比較の一致を、元の全 Hom の fiber 判定へ接続する。
規約：元の比較そのものの同値性を証明し、一般の底の大域分類とは区別する。
使われ方：一般の Cat∞ 値分類の高次セルと大域充満忠実性へ進む。

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
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomIntervalEvaluation_fibration
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent F G c) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalMappingCore_one_fibration F G
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F.val G.val c)))
  infer_instance

/-- 元の一次元の固定成分比較そのものは、全ての指定成分で同値。 -/
lemma cocartesianHomFixedComponentComparison_isQCatEquivalence
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomFixedComponentComparison F G c b) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionHomCriterion.cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_postcomposition F G b).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionDiagonalCriterion.cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff F G b).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionComparisonEquivalence.cocartesianPostcompositionDiagonalComparison_isQCatEquivalence F G b)

/-- 元の実際の輸送図式の区間 Hom 作用は、追加仮定なしに同値。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval F G) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_fixedComponent F G).mpr
  exact fun b ↦ cocartesianHomFixedComponentComparison_isQCatEquivalence F G b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
