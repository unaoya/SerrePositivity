module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorWord
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality

/-!
# 自由圏の元の全縦射による各列の非指定文字列の不変性

概要：各列の非指定生成文字列は元の全縦指定射で保存され、後ろ向き列では空になる。
方針：元の Zigzag.Hom.comm の正方形と元の backward_mem を消去操作に渡す。
規約：各元の列と全縦射を保持する。
使われ方：各行を同じ非指定生成文字の位置で分解する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C}

def column (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length) : List (Quiver.Total C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (S.arrow i)

lemma column_hom {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y} (f : S ⟶ T) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W T i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_square W (S.arrow i) (T.arrow i)
    (f.app (w.source i)) (f.app (w.target i))
    (f.app_mem (w.source i)) (f.app_mem (w.target i)) (f.comm i)

lemma column_backward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i = [] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W (S.arrow i) (S.backward_mem i hi)

lemma column_row {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n)
    (k : Fin (n.unop.len + 1)) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj k) i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_hom W (τ.map (homOfLE (Fin.zero_le k))) i).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns
