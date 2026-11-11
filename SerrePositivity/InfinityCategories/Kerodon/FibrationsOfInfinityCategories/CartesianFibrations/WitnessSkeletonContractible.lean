module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessSkeleton
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ContractibleKanTower

/-!
概要：全ての有限骨格での表現空間の可縮性から大域の可縮性を導く。
方針：骨格の厳密な逆極限と遷移の Kan fibration 性を組み合わせる。
規約：各骨格の可縮性はこの補題では入力とする。
使われ方：セルの帰納法を一般の底へ延ばす最終段階。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：各有限骨格上の表現空間が可縮なら元の表現空間も可縮。
方針：骨格の制限の fibration 塔の極限に可縮性を移す。
規約：骨格の可縮性を単に極限保存だけから推論しない。
使われ方：一般の底上の表現空間の可縮性の骨格による還元。 -/
lemma transportWitnessSpace_isContractibleKan_of_skeleton {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
      (Opposite.op ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSkeletonOver B).obj n)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  have : ∀ n, Fibration (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSkeletonOver B).op ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).map (homOfLE (Nat.le_succ n)).op) :=
    fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSkeleton_map_fibration p (homOfLE (Nat.le_succ n))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isContractibleKan_of_fibrationTowerCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSkeletonCone p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSkeletonCone_isLimit_actual p) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
