module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentBlockComparison

/-!
# 元の連続部分の方向付き列の回収

概要：元の頂点・生の列を保持する連続部分は方向付きの列も保持する。
方針：元の始域・終域の等式と生の列の異種等式を方向の比較へ渡す。
規約：元の圏と反対圏の両方向を含む。
使われ方：前後の語から抽出した列の元の方向付き列への照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y X' Y' : C}

lemma block_arrow_heq (B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Block a b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X' Y')
    (hv : ∀ j, T.vertex (B.vertex j) = S.vertex j)
    (ha : ∀ j, HEq (T.arrow (B.column j)) (S.arrow j))
    (δ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin a.length) (hi : a.direction i = δ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ T (B.column i) ((B.direction_eq i).trans hi)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow δ S i hi) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_heq_of T S δ _ _ _ _
    ((congrArg T.vertex (B.source_eq i)).trans (hv (a.source i)))
    ((congrArg T.vertex (B.target_eq i)).trans (hv (a.target i))) (ha i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (block_arrow_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
