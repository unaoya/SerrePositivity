module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionComparisonEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionDiagonalCriterion

/-!
概要：実際の輸送図式の一次元 Hom の元の作用は同値。
方針：元の後合成 fiber 比較と標準比較の一致を、元の全 Hom の fiber 判定へ接続する。
規約：元の比較そのものの同値性を証明し、一般の底の大域分類とは区別する。
使われ方：一般の Cat∞ 値分類の高次セルと大域充満忠実性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))

attribute [local instance] cocartesianHomIntervalEvaluation_fibration
attribute [local instance] vertexFiber_quasicategory_of_innerFibration

local instance : LeftFibration (cocartesianHomSourceComponent F G c) := by
  letI := cocartesianIntervalMappingCore_one_fibration F G
  change LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreMap
    (strictDiagramMappingComponent F.val G.val c)))
  infer_instance

/-- 元の一次元の固定成分比較そのものは、全ての指定成分で同値。 -/
lemma cocartesianHomFixedComponentComparison_isQCatEquivalence
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G c))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianHomFixedComponentComparison F G c b) := by
  apply (cocartesianHomFixedComponentComparison_isQCatEquivalence_iff_postcomposition F G b).mpr
  exact (cocartesianPostcompositionDiagonalComparison_isQCatEquivalence_iff F G b).mp
    (cocartesianPostcompositionDiagonalComparison_isQCatEquivalence F G b)

/-- 元の実際の輸送図式の区間 Hom 作用は、追加仮定なしに同値。 -/
lemma cocartesianTransportDiagramHomInterval_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTransportDiagramHomInterval F G) := by
  apply (cocartesianTransportDiagramHomInterval_isQCatEquivalence_iff_fixedComponent F G).mpr
  exact fun b ↦ cocartesianHomFixedComponentComparison_isQCatEquivalence F G b

end SerrePositivity.InfinityCategories
