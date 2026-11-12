module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstCut

/-!
# 固定した非指定生成矢での元の切断表示

概要：最初の非指定生成矢の始域・終域・射を固定した切断を構成する。
方針：FirstCut の Total 等式で表示を揃え、元の切断の一意性を使う。
規約：元の射列の因子化と指定接頭列を保持する。
使われ方：全行の切断を同じ固定生成矢で関手へ束ねる。

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

structure FixedCut (a : Quiver.Total C) {X Y : C} (p : Quiver.Path X Y) where
  left : Quiver.Path X a.left
  right : Quiver.Path a.right Y
  left_mem : W.paths left
  unmarked : ¬ W a.hom
  factorization : p = left.comp (a.hom.toPath.comp right)

def FixedCut.toFirstCut {a : Quiver.Total C} {X Y : C} {p : Quiver.Path X Y}
    (P : FixedCut W a p) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W p :=
  ⟨a.left, a.right, a.hom, P.left, P.right, P.left_mem, P.unmarked, P.factorization⟩

def FixedCut.ofFirstCut {a : Quiver.Total C} {X Y : C} {p : Quiver.Path X Y}
    (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstCut W p) (h : (⟨P.source, P.target, P.arrow⟩ : Quiver.Total C) = a) :
    FixedCut W a p := by
  rcases a with ⟨A, B, e⟩
  rcases P with ⟨A', B', e', left, right, hl, he, hp⟩
  dsimp only at h
  obtain ⟨hA, hB, harrow⟩ := Quiver.Total.mk.inj h
  subst A'
  subst B'
  have hea : e' = e := eq_of_heq harrow
  subst e'
  exact ⟨left, right, hl, he, hp⟩

lemma fixedCut_ext {a : Quiver.Total C} {X Y : C} {p : Quiver.Path X Y}
    (P Q : FixedCut W a p) : P = Q := by
  rcases P with ⟨left, right, hl, he, hp⟩
  rcases Q with ⟨left', right', hl', he', hq⟩
  obtain ⟨hleft, hright⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.first_split_same_arrow W a.hom left left' right right'
    hl hl' he (hp.symm.trans hq)
  subst left'
  subst right'
  rfl

instance fixedCut_subsingleton {a : Quiver.Total C} {X Y : C} (p : Quiver.Path X Y) :
    Subsingleton (FixedCut W a p) := ⟨fixedCut_ext W⟩

lemma FixedCut.square {a : Quiver.Total C} {X Y X' Y' : C}
    {p : Quiver.Path X Y} {q : Quiver.Path X' Y'} (P : FixedCut W a p) (Q : FixedCut W a q)
    (u : Quiver.Path X X') (v : Quiver.Path Y Y') (hu : W.paths u)
    (h : p.comp v = u.comp q) : P.left = u.comp Q.left ∧ P.right.comp v = Q.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.first_split_square_same_arrow W p q u v hu a.hom P.left P.right Q.left Q.right
    P.left_mem Q.left_mem P.unmarked P.factorization Q.factorization h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
