module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumnWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentErasure

/-!
# 元の最初の非指定列を含む fiber の非指定文字列

概要：元の最小非指定列の文字列は、その像の列の文字列の接頭列である。
方針：fiber を元の一列の前後で分割し、その前の指定区間の文字列を消す。
規約：同じ元の列と生成文字を保持し、後ろの区間の指定性は仮定しない。
使われ方：語の圧縮による最初の非指定生成矢の保持。

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

lemma firstFiber_erasure_prefix : ∃ tail : List (Quiver.Total C),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h) ++ tail := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h
  let j := f.orderHom i
  let p := f.cut j.castSucc
  let q := f.cut j.succ
  have hpq : p ≤ q := f.cut_monotone (Fin.castSucc_le_succ j)
  have hb : p.val ≤ i.val ∧ i.val < q.val := (f.fiber_iff j i).2 rfl
  have hj : b.direction j = .forward := (f.direction_eq i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W S h)
  let hd := fun k hk hk' => (f.fiber_direction j k hk hk').trans hj
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_forward_arrow W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj).symm.trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W) (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S .forward j hj)))
  have hl : W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p i.castSucc hb.1
      (fun k hk hk' => hd k hk (by change k.val < i.val at hk'; omega))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_map_mem S p i.castSucc hb.1 _ W.paths
    intro k _ hk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_mem W S h k hk
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_forward_map_split W S p q hpq hd i hb.1 hb.2
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W _ hl, List.nil_append] at hs
  exact ⟨_, he.trans hs⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
