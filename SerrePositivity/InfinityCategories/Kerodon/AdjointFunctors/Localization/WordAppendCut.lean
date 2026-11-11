module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCut

/-!
# 連結した語の写像の切断位置

概要：連結した写像の左右の全頂点の切断を、元の二つの切断と照合する。
方針：左側の列を特徴付ける不等式を有限順序の直和の両部分で比較する。
規約：接合点を左右のどちらで表しても、同じ元の切断位置となる。
使われ方：zigzag の連結と全語の遷移の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 左部分の全頂点の切断は、元の左の切断。 -/
lemma cut_append_left {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b')
    (j : Fin (a'.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a' b' j) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (f.cut j) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.vertex_ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.lt_cut_iff]
  cases i using Fin.addCases with
  | left i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_left f g i]
    change (f.orderHom i).val < j.val ↔ i.val < (f.cut j).val
    exact (f.lt_cut_iff j i).symm
  | right i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_right f g i]
    change a'.length + (g.orderHom i).val < j.val ↔ a.length + i.val < (f.cut j).val
    have := j.isLt
    have := (f.cut j).isLt
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cut_append_left)


/-- 右部分の全頂点の切断は、元の右の切断を左の長さだけずらした位置。 -/
lemma cut_append_right {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b')
    (j : Fin (b'.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a' b' j) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b (g.cut j) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.vertex_ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.lt_cut_iff]
  cases i using Fin.addCases with
  | left i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_left f g i]
    change (f.orderHom i).val < a'.length + j.val ↔ i.val < a.length + (g.cut j).val
    have := (f.orderHom i).isLt
    have := i.isLt
    omega
  | right i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_right f g i]
    change a'.length + (g.orderHom i).val < a'.length + j.val ↔
      a.length + i.val < a.length + (g.cut j).val
    have := g.lt_cut_iff j i
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cut_append_right)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
