module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedSplitSquare

/-!
# 元の射列の一意な最初の非指定切断

概要：元の指定接頭列・最初の非指定生成矢・残りを、存在と一意性を持つデータに束ねる。
方針：元の切断の存在・Total 矢と射列の一意性を使う。
規約：切断の存在や自然性を未証明の入力にしない。
使われ方：hammock の各列の切断を全縦射に沿って比較する。

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

structure FirstCut {X Y : C} (p : Quiver.Path X Y) where
  source : C
  target : C
  arrow : source ⟶ target
  left : Quiver.Path X source
  right : Quiver.Path target Y
  left_mem : W.paths left
  unmarked : ¬ W arrow
  factorization : p = left.comp (arrow.toPath.comp right)

lemma firstCut_ext {X Y : C} {p : Quiver.Path X Y} (P Q : FirstCut W p) : P = Q := by
  rcases P with ⟨A, B, e, left, right, hl, he, hp⟩
  rcases Q with ⟨A', B', e', left', right', hl', he', hq⟩
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.first_split_unique W e e' left right left' right' hl hl' he he' (hp.symm.trans hq)
  obtain ⟨hA, hB, harrow⟩ := Quiver.Total.mk.inj hh.1
  subst A'
  subst B'
  have hea : e = e' := eq_of_heq harrow
  subst e'
  have hleft : left = left' := eq_of_heq hh.2.1
  have hright : right = right' := eq_of_heq hh.2.2
  subst left'
  subst right'
  rfl

instance firstCut_subsingleton {X Y : C} (p : Quiver.Path X Y) : Subsingleton (FirstCut W p) :=
  ⟨firstCut_ext W⟩

lemma firstCut_nonempty_iff {X Y : C} (p : Quiver.Path X Y) :
    Nonempty (FirstCut W p) ↔ ¬ W.paths p := by
  constructor
  · rintro ⟨P⟩ hp
    rw [P.factorization] at hp
    exact P.unmarked ((W.comp_mem_paths_iff.1 (W.comp_mem_paths_iff.1 hp).2).1.2)
  · intro hp
    obtain ⟨A, B, e, left, right, hl, he, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_first_unmarked W p hp
    exact ⟨⟨A, B, e, left, right, hl, he, h⟩⟩

def firstCut {X Y : C} (p : Quiver.Path X Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p ≠ []) : FirstCut W p :=
  Classical.choice ((firstCut_nonempty_iff W p).2 (fun h => hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W p h)))

lemma firstCut_erasure {X Y : C} {p : Quiver.Path X Y} (P : FirstCut W p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p = ⟨P.source, P.target, P.arrow⟩ :: _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W P.right := by
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W) P.factorization).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_first_split W P.left P.arrow P.right P.left_mem P.unmarked)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
