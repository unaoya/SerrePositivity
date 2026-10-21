module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackAnodyneRestriction
public import SerrePositivity.InfinityCategories.F1.HigherHornEdgeCover

/-!
概要：三次元以上の内ホーンへの元の cocartesian Hom の制限は自明 Kan 同値。
方針：内ホーンは inner anodyne で全辺を含むため、元の指定辺保存 Hom の制限定理を適用する。
規約：底変換後の両射影を持つ元の cocartesian Hom の core そのものを扱う。
使われ方：分類の Hom 比較を高次ホーンの付加に沿って運ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 三次元以上の内ホーンへの元の cocartesian Hom の core の制限は自明 Kan。 -/
lemma core_cocartesianPullbackNativeRestriction_higherInnerHorn_trivialKanFibration
    {n : ℕ} (hn : 3 ≤ n) (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u}))
    [CocartesianFibration p] (q : F ⟶ (Δ[n] : SSet.{u}))
    [CocartesianFibration q] :
    TrivialKanFibration (quasicategoryCoreMap
      (cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) :=
  core_cocartesianPullbackNativeRestriction_trivialKanFibration p q _
    (innerAnodyneExtensions.horn_ι h0 hk) (horn_ι_edge_surjective_of_three_le hn k)

/-- 同じ高次内ホーンへの元の Hom の core の制限は、追加仮定なしに同値。 -/
lemma core_cocartesianPullbackNativeRestriction_higherInnerHorn_isQCatEquivalence
    {n : ℕ} (hn : 3 ≤ n) (k : Fin (n + 1)) (h0 : 0 < k) (hk : k < Fin.last n)
    {E F : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u}))
    [CocartesianFibration p] (q : F ⟶ (Δ[n] : SSet.{u}))
    [CocartesianFibration q] :
    IsQCatEquivalence (quasicategoryCoreMap
      (cocartesianPullbackNativeRestriction p q (Over.mk (horn n k).ι))) := by
  letI := core_cocartesianPullbackNativeRestriction_higherInnerHorn_trivialKanFibration hn k h0 hk p q
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
