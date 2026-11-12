module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerTwoHornRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HigherHornRestriction

/-!
概要：全ての内ホーンへの、元の cocartesian Hom の core の制限は自明 Kan 同値。
方針：二次元の長辺の反映と、三次元以上の全辺の被覆を合わせる。
規約：元の両射影を底変換した同じ Hom を使用し、追加仮定を置かない。
使われ方：高次単体の Hom 比較と、inner anodyne な底の生成元での降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 任意の内ホーンへの元の cocartesian Hom の core の制限は自明 Kan。 -/
lemma core_cocartesianPullbackNativeRestriction_innerHorn_trivialKanFibration
    {n : ℕ} (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (q : F ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) := by
  by_cases hn : 3 ≤ n
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativeRestriction_higherInnerHorn_trivialKanFibration hn k h0 hk p q
  have hn : n = 2 := by omega
  subst n
  have hkv : k = 1 := by
    have hk0 : 0 < k.val := h0
    have hk2 : k.val < 2 := hk
    apply Fin.ext
    change k.val = 1
    omega
  subst k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativeRestriction_innerTwoHorn_trivialKanFibration p q

/-- 任意の内ホーンへの元の Hom の core の同じ制限は同値。 -/
lemma core_cocartesianPullbackNativeRestriction_innerHorn_isQCatEquivalence
    {n : ℕ} (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (q : F ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) := by
  letI := core_cocartesianPullbackNativeRestriction_innerHorn_trivialKanFibration k h0 hk p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
