module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackAnodyneRestriction
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HigherHornEdgeCover

/-!
概要：三次元以上の内ホーンへの元の cocartesian Hom の制限は自明 Kan 同値。
方針：内ホーンは inner anodyne で全辺を含むため、元の指定辺保存 Hom の制限定理を適用する。
規約：底変換後の両射影を持つ元の cocartesian Hom の core そのものを扱う。
使われ方：分類の Hom 比較を高次ホーンの付加に沿って運ぶ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 三次元以上の内ホーンへの元の cocartesian Hom の core の制限は自明 Kan。 -/
lemma core_cocartesianPullbackNativeRestriction_higherInnerHorn_trivialKanFibration
    {n : ℕ} (hn : 3 ≤ n) (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u}))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ (Δ[n] : SSet.{u}))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativeRestriction_trivialKanFibration p q _
    (innerAnodyneExtensions.horn_ι h0 hk) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horn_ι_edge_surjective_of_three_le hn k)

/-- 同じ高次内ホーンへの元の Hom の core の制限は、追加仮定なしに同値。 -/
lemma core_cocartesianPullbackNativeRestriction_higherInnerHorn_isQCatEquivalence
    {n : ℕ} (hn : 3 ≤ n) (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u}))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ (Δ[n] : SSet.{u}))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) := by
  letI := core_cocartesianPullbackNativeRestriction_higherInnerHorn_trivialKanFibration hn k h0 hk p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
