module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairLoops
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeMappingContractible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingRestriction

/-! # 零枝の余錐空間の自己引き戻しとループ模型

概要：始対象へ向かう辺の余錐空間の自己引き戻しは、始点余錐空間の基点付きループ模型と同値。
方針：余錐制限の Kan fibration 性と枝の可縮性を、可縮な全空間の自己引き戻しの比較へ与える。
規約：基点となる枝の余錐を入力する。使われ方：対称 suspension の二枝の引き戻しのループ表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：辺の終点固定余錐を辺の始点に制限する。
方針：標準辺の始点の包含による coslice fiber の制限を使う。
規約：終点 y を保つ。使われ方：対称 span の両枝から共通始点への射。 -/
def coconeBranchSource {X : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ f) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap f (stdSimplex.δ (1 : Fin 2)) y

/-- 概要：枝の余錐から始点の余錐への制限は Kan fibration。
方針：単射による余錐空間の制限の充填性を使う。
規約：値域は quasicategory。使われ方：二枝の自己引き戻しを固定点の fiber へ比較する。 -/
instance coconeBranchSource_fibration {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) : Fibration (coconeBranchSource f y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_fibration f (stdSimplex.δ (1 : Fin 2)) y

/-- 概要：可縮な枝の自己引き戻しから共通始点の余錐空間のループ模型への比較。
方針：枝の可縮性を kernel pair の一般の比較射へ適用する。
規約：辺の終点の始対象性と枝の余錐の基点を指定する。使われ方：対称 suspension の交換のループ表示。 -/
def coconeBranchKernelPairLoopComparison {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ f)))
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f y) _⦋0⦌) :
    pullback (coconeBranchSource f y) (coconeBranchSource f y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft ((coconeBranchSource f y).app (Opposite.op ⦋0⦌) e)
        ((coconeBranchSource f y).app (Opposite.op ⦋0⦌) e) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopComparison (coconeBranchSource f y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan f hz y) e

/-- 概要：枝の自己引き戻しから共通始点の余錐空間のループ模型への比較はホモトピー同値。
方針：両余錐空間の Kan 性と枝の可縮性を一般の比較の同値性へ与える。
規約：安定性全体は不要。使われ方：二枝の引き戻しをループ空間で扱うための同値。 -/
lemma coconeBranchKernelPairLoopComparison_homotopyEquivalence {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ f)))
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coconeBranchKernelPairLoopComparison f hz y e) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopComparison_homotopyEquivalence (coconeBranchSource f y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan f hz y) e

/-- 概要：枝の自己引き戻しの連結成分は共通始点の余錐空間の基点の自己射と同値。
方針：一般の kernel pair の連結成分とループの Hom 同値を特殊化する。
規約：この自己射は Kan 複体のホモトピー圏の射。使われ方：二枝交換を逆射として読む比較。 -/
def coconeBranchKernelPairPiZeroLoopEquiv {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ f)))
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f y) _⦋0⦌) :
    SSet.π₀ (pullback (coconeBranchSource f y) (coconeBranchSource f y)) ≃
      ((SSet.HomotopyCategory.mk ((coconeBranchSource f y).app (Opposite.op ⦋0⦌) e) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ f) y)) ⟶
          SSet.HomotopyCategory.mk ((coconeBranchSource f y).app (Opposite.op ⦋0⦌) e)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv (coconeBranchSource f y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan f hz y) e

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
