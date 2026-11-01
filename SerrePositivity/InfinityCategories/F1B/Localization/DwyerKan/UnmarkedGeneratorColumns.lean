module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedGeneratorWord
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentNaturality

/-!
# 自由圏の元の全縦射による各列の非指定文字列の不変性

概要：各列の非指定生成文字列は元の全縦指定射で保存され、後ろ向き列では空になる。
方針：元の Zigzag.Hom.comm の正方形と元の backward_mem を消去操作に渡す。
規約：各元の列と全縦射を保持する。
使われ方：各行を同じ非指定生成文字の位置で分解する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C}

def column (S : Zigzag W.paths w X Y) (i : Fin w.length) : List (Quiver.Total C) :=
  GeneratorWord.erase W (S.arrow i)

lemma column_hom {S T : Zigzag W.paths w X Y} (f : S ⟶ T) (i : Fin w.length) :
    column W S i = column W T i :=
  GeneratorWord.erase_square W (S.arrow i) (T.arrow i)
    (f.app (w.source i)) (f.app (w.target i))
    (f.app_mem (w.source i)) (f.app_mem (w.target i)) (f.comm i)

lemma column_backward (S : Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) : column W S i = [] :=
  GeneratorWord.erase_marked W (S.arrow i) (S.backward_mem i hi)

lemma column_row {n : SimplexCategoryᵒᵖ} (τ : (graph W.paths w X Y).obj n)
    (k : Fin (n.unop.len + 1)) (i : Fin w.length) :
    column W (τ.obj k) i = column W (τ.obj 0) i :=
  (column_hom W (τ.map (homOfLE (Fin.zero_le k))) i).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
