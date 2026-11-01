module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingFull
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.NerveFullRange
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 語の包含による元の graph の全単体の像

概要：包含の全単体の像を、元の各頂点の zigzag の像で特徴付ける。
方針：構成済みの元の遷移の充満忠実性と全射列の回収を使う。
規約：元の対象の等式と元の全縦射を保持する。
使われ方：部分語の列の像による graph の像の交わりの比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {a b : Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : C)
include hf

/-- 元の全次数の包含の像は、元の各行の zigzag の像から決まる。 -/
lemma graphDiagram_map_range_iff (n : SimplexCategoryᵒᵖ) (τ : (graph W b X Y).obj n) :
    τ ∈ Set.range (((graphDiagram W X Y).map f).app n) ↔
      ∀ j, ∃ S : Zigzag W a X Y, WordAction.obj f S = τ.obj j := by
  rw [graphDiagram_map]
  have := WordAction.functor_full (W := W) (X := X) (Y := Y) f hf
  have := WordAction.functor_faithful (W := W) (X := X) (Y := Y) f hf
  exact nerveMap_range_iff _ τ

end SerrePositivity.EInfinity.Hammock
