module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessCartesianRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPullbackFunctor

/-!
概要：底上の降下関手の実際の遷移射の充填性。
方針：底変換関手の正方形が pullback であることを一般の制限定理へ適用する。
規約：遷移射の左成分に単射性または inner anodyne 性を指定する。
使われ方：骨格列とセルの表現空間を Kan fibration で結ぶ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底上の単射は降下の表現空間の Kan fibration を誘導する。
方針：底変換の関手の pullback 正方形に一般の充填性を適用する。
規約：射の基礎の単体集合の単射性を使う。
使われ方：骨格の隣接段への制限。 -/
lemma transportWitnessPullbackFunctor_map_fibration {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : Over B} (f : a ⟶ b) [Mono f.left] :
    Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).map f.op) := by
  change Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor_isPullback p f))
  have : Mono (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map f).right) := by
    change Mono f.left
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_fibration _ _

/-- 概要：底上の inner anodyne 射は降下の表現空間の trivial Kan fibration を誘導する。
方針：底変換の正方形に一般の全境界充填を適用する。
規約：全空間側の表示を固定しない。
使われ方：内ホーンから標準単体への延長。 -/
lemma transportWitnessPullbackFunctor_map_trivialKanFibration {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : Over B} (f : a ⟶ b)
    (h : innerAnodyneExtensions f.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).map f.op) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor_isPullback p f))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_trivialKanFibration
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
