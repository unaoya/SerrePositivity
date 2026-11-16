module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphEmbedding
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphEmbeddingRange

/-!
# 元の E 代数の包含の充満性と全単体の像

概要：任意の可換環上の元の包含の全縦射を回収し、全単体の像を各行で特徴付ける。
方針：元の弱同値に構成済みの回収と充満性を代入する。
規約：モデル構造は局所的に選び、モデルの追加入力や対象の cofibrancy は不要。
使われ方：同じ E 代数の全語の図式の proper 性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
  (hf : Function.Injective f.orderHom) (X Y : (operad A).Algebra)
include hf

lemma algebraHammockTransition_full : (algebraHammockTransition A f X Y).Full := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_full f hf

/-- 同じ元の包含の像の間の全縦射を回収する。 -/
def algebraHammockTransitionPreimage {S T : algebraHammockZigzag A a X Y}
    (g : (algebraHammockTransition A f X Y).obj S ⟶
      (algebraHammockTransition A f X Y).obj T) : S ⟶ T := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embeddingPreimage f hf g

lemma algebraHammockTransition_map_preimage {S T : algebraHammockZigzag A a X Y}
    (g : (algebraHammockTransition A f X Y).obj S ⟶
      (algebraHammockTransition A f X Y).obj T) :
    (algebraHammockTransition A f X Y).map (algebraHammockTransitionPreimage A f hf X Y g) =
      g := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_embeddingPreimage f hf g

lemma algebraHammockTransition_preimage_map {S T : algebraHammockZigzag A a X Y} (g : S ⟶ T) :
    algebraHammockTransitionPreimage A f hf X Y ((algebraHammockTransition A f X Y).map g) =
      g := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embeddingPreimage_map f hf g

/-- 同じ元の全単体の像は、元の全ての行の対象の像で特徴付けられる。 -/
lemma algebraHammockGraphMap_range_iff (n : SimplexCategoryᵒᵖ)
    (τ : (algebraHammockGraph A b X Y).obj n) :
    τ ∈ Set.range ((algebraHammockGraphMap A f X Y).app n) ↔
      ∀ j, ∃ S : algebraHammockZigzag A a X Y, (algebraHammockTransition A f X Y).obj S =
        τ.obj j := by
  have := algebraHammockTransition_full A f hf X Y
  have := algebraHammockTransition_faithful A f hf X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nerveMap_range_iff _ τ

end SerrePositivity.EInfinity.BarrattEccles
