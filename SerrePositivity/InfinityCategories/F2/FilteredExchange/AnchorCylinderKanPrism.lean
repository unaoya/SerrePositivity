module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.AnchorCylinderCoordinates
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanPrismExtension
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling

/-!
概要：有限因子分解の新しい単射な境界への補正を Kan 模型の円柱で実現する。
方針：元の境界を新しい円柱の終点へ動かす部分円柱を全形状へ延長する。
規約：全円柱の始点と部分円柱を厳密に保持する。
使われ方：境界の単射性を保つ相対有限近似。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の Kan 射の境界を新しい単射な境界へ動かす全円柱。
方針：単位の自然性で部分円柱の始点を合わせ、Kan 標的の部分円柱延長を使う。
規約：有限性はこの延長自体には不要。使われ方：有限な単射境界の補正。 -/
lemma anchorCylinder_kan_prism {A K L : SSet.{u}} (i : A ⟶ K) [Mono i] (a : A ⟶ L)
    (r : K ⟶ continuousKanReplacement.obj L)
    (h : i ≫ r = a ≫ continuousKanReplacementUnit.app L) :
    ∃ R : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj (anchorCylinder a),
      SSet.ι₀ ≫ R = r ≫ continuousKanReplacement.map
        (pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a) ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ R =
        pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a ≫
          continuousKanReplacementUnit.app (anchorCylinder a) := by
  let j := pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a
  let t := pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a
  have hn : j ≫ continuousKanReplacementUnit.app (anchorCylinder a) =
      continuousKanReplacementUnit.app L ≫ continuousKanReplacement.map j :=
    continuousKanReplacementUnit.naturality j
  apply kan_prism_extension i (r ≫ continuousKanReplacement.map j)
    (t ≫ continuousKanReplacementUnit.app (anchorCylinder a))
  rw [← Category.assoc, show SSet.ι₀ ≫ t = a ≫ j from anchorCylinder_prism_zero a,
    Category.assoc, hn, ← Category.assoc, ← h, Category.assoc]

end SerrePositivity.InfinityCategories.F2
