module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentBlockComparison

/-!
# 元の連続部分の方向付き列の回収

概要：元の頂点・生の列を保持する連続部分は方向付きの列も保持する。
方針：元の始域・終域の等式と生の列の異種等式を方向の比較へ渡す。
規約：元の圏と反対圏の両方向を含む。
使われ方：前後の語から抽出した列の元の方向付き列への照合。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Direction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word}
  {X Y X' Y' : C}

lemma block_arrow_heq (B : Word.Block a b) (S : Zigzag W a X Y) (T : Zigzag W b X' Y')
    (hv : ∀ j, T.vertex (B.vertex j) = S.vertex j)
    (ha : ∀ j, HEq (T.arrow (B.column j)) (S.arrow j))
    (δ : Direction) (i : Fin a.length) (hi : a.direction i = δ) :
    HEq (arrow δ T (B.column i) ((B.direction_eq i).trans hi)) (arrow δ S i hi) :=
  arrow_heq_of T S δ _ _ _ _
    ((congrArg T.vertex (B.source_eq i)).trans (hv (a.source i)))
    ((congrArg T.vertex (B.target_eq i)).trans (hv (a.target i))) (ha i)

end SerrePositivity.EInfinity.Hammock.Direction
