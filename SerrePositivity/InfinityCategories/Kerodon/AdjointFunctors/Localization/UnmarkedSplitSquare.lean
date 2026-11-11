module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedSplitUnique

/-!
# 元の指定縦射の正方形の最初の非指定生成矢での切断

概要：元の正方形から同じ非指定生成矢、指定接頭列の正方形、残りの正方形を回収する。
方針：両辺の元の連結を同じ最初の切断へ戻し、その一意性を使う。
規約：元の指定縦射 u・v と元の正方形そのものを保持する。
使われ方：hammock の全行を同じ非指定生成矢で切る。

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

lemma first_split_square {X Y X' Y' A B A' B' : C}
    (p : Quiver.Path X Y) (q : Quiver.Path X' Y')
    (u : Quiver.Path X X') (v : Quiver.Path Y Y') (hu : W.paths u)
    (e : A ⟶ B) (e' : A' ⟶ B') (left : Quiver.Path X A) (right : Quiver.Path B Y)
    (left' : Quiver.Path X' A') (right' : Quiver.Path B' Y')
    (hl : W.paths left) (hl' : W.paths left') (he : ¬ W e) (he' : ¬ W e')
    (hp : p = left.comp (e.toPath.comp right))
    (hq : q = left'.comp (e'.toPath.comp right')) (h : p.comp v = u.comp q) :
    (⟨A, B, e⟩ : Quiver.Total C) = ⟨A', B', e'⟩ ∧
      HEq left (u.comp left') ∧ HEq (right.comp v) right' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.first_split_unique W e e' left (right.comp v) (u.comp left') right'
    hl (W.comp_mem_paths_iff.2 ⟨hu, hl'⟩) he he'
  simpa only [hp, hq, Quiver.Path.comp_assoc] using h

lemma first_split_square_same_arrow {X Y X' Y' A B : C}
    (p : Quiver.Path X Y) (q : Quiver.Path X' Y')
    (u : Quiver.Path X X') (v : Quiver.Path Y Y') (hu : W.paths u)
    (e : A ⟶ B) (left : Quiver.Path X A) (right : Quiver.Path B Y)
    (left' : Quiver.Path X' A) (right' : Quiver.Path B Y')
    (hl : W.paths left) (hl' : W.paths left') (he : ¬ W e)
    (hp : p = left.comp (e.toPath.comp right))
    (hq : q = left'.comp (e.toPath.comp right')) (h : p.comp v = u.comp q) :
    left = u.comp left' ∧ right.comp v = right' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.first_split_same_arrow W e left (u.comp left') (right.comp v) right'
    hl (W.comp_mem_paths_iff.2 ⟨hu, hl'⟩) he
  simpa only [hp, hq, Quiver.Path.comp_assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
