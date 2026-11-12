module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberErasure
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnCutSquare
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCutPrefix

/-!
# 元の語の圧縮による最初の非指定生成矢の保持

概要：最小非指定列とその像の切断は、同じ元の Total 生成矢を持つ。
方針：元の列の文字列が像の文字列の接頭列であることと切断の消去式を使う。
規約：元の自由圏の生成射を保持し、像の後置部分に条件を置かない。
使われ方：prefix と残りの全語への整合と積分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y)
  (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [])

lemma firstFiber_generator
    (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W (S.arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)))
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).arrow (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)))) :
    (⟨Q.source, Q.target, Q.arrow⟩ : Quiver.Total C) = ⟨P.source, P.target, P.arrow⟩ := by
  obtain ⟨tail, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstFiber_erasure_prefix W f S h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstCut_generator_of_erasure_prefix W Q P tail ht

lemma firstFiber_columnFirstCut :
    let P := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnFirstCut W S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W S h)
    let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnFirstCut W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_wordAction_nonempty W f S _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W S h))
    (⟨Q.source, Q.target, Q.arrow⟩ : Quiver.Total C) = ⟨P.source, P.target, P.arrow⟩ :=
  firstFiber_generator W f S h _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
