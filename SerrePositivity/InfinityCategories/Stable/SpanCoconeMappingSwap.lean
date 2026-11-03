module
public import SerrePositivity.InfinityCategories.F1.SpanCoconeMappingPullback
public import SerrePositivity.InfinityCategories.F1.SquareTranspose

/-! # 二枝交換と余錐空間の枝の交換

概要：span の二枝を交換して余錐を制限すると、二枝への制限が互いに入れ替わる。
方針：uncurry した余錐の join による制限を計算する。
規約：形状の等号による表示の変更を避け、余錐そのものの等号で述べる。
使われ方：HA Lemma 1.1.2.10 の D(σ) 上の involution。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：枝を交換した余錐の第一枝への制限は元の第二枝への制限である。
方針：join の合成をまとめ、spanSwap_left を使う。
規約：任意パラメーター、値域の仮定なし。使われ方：比較空間の交換作用の第一成分。 -/
lemma coconeMappingSpace_spanSwap_left {X T : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌) (a : T ⟶ coconeMappingSpace p y) :
    joinMap horn₂₀.ι₀₁ (𝟙 T) ≫ sliceUnderUncurry
      ((a ≫ cosliceRestrictionFiberMap p spanSwap y) ≫
        vertexFiberι (sliceUnderProjection (spanSwap ≫ p)) y) =
    joinMap horn₂₀.ι₀₂ (𝟙 T) ≫
      sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection p) y) := by
  rw [coconeMappingSpace_restrict_uncurry, ← Category.assoc, ← joinMap_comp,
    spanSwap_left, Category.comp_id]

/-- 概要：枝を交換した余錐の第二枝への制限は元の第一枝への制限である。
方針：join の合成をまとめ、spanSwap_right を使う。
規約：任意パラメーター、値域の仮定なし。使われ方：比較空間の交換作用の第二成分。 -/
lemma coconeMappingSpace_spanSwap_right {X T : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌) (a : T ⟶ coconeMappingSpace p y) :
    joinMap horn₂₀.ι₀₂ (𝟙 T) ≫ sliceUnderUncurry
      ((a ≫ cosliceRestrictionFiberMap p spanSwap y) ≫
        vertexFiberι (sliceUnderProjection (spanSwap ≫ p)) y) =
    joinMap horn₂₀.ι₀₁ (𝟙 T) ≫
      sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection p) y) := by
  rw [coconeMappingSpace_restrict_uncurry, ← Category.assoc, ← joinMap_comp,
    spanSwap_right, Category.comp_id]

end SerrePositivity.InfinityCategories
