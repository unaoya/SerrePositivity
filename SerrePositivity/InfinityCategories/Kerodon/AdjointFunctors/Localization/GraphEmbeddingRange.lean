module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingFull
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.NerveFullRange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 語の包含による元の graph の全単体の像

概要：包含の全単体の像を、元の各頂点の zigzag の像で特徴付ける。
方針：構成済みの元の遷移の充満忠実性と全射列の回収を使う。
規約：元の対象の等式と元の全縦射を保持する。
使われ方：部分語の列の像による graph の像の交わりの比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : C)
include hf

/-- 元の全次数の包含の像は、元の各行の zigzag の像から決まる。 -/
lemma graphDiagram_map_range_iff (n : SimplexCategoryᵒᵖ) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n) :
    τ ∈ Set.range (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n) ↔
      ∀ j, ∃ S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S = τ.obj j := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram_map]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_full (W := W) (X := X) (Y := Y) f hf
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor_faithful (W := W) (X := X) (Y := Y) f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nerveMap_range_iff _ τ

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
