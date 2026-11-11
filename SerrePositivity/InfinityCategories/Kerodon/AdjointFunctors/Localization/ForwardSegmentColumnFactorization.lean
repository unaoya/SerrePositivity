module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentMarked

/-!
# 元の forward 区間の合成と同じ元の列を挟む前後の射

概要：内部の生の列を保持し、前後の区間に元の端点移送を接続する。
方針：元の同方向三分割の方向付き列を元の射へ展開する。
規約：同型類ではなく元の射の等式を証明する。
使われ方：語の圧縮の最初の切断の前後の射列の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward)
  (i : Fin w.length) (hp : p.val ≤ i.val) (hq : i.val < q.val)

def toColumn : S.vertex p ⟶ S.vertex (w.source i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p i.castSucc hp
    (fun j hj hj' => hd j hj (by change j.val < i.val at hj'; omega)) ≫
      eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hd i hp hq]))

def fromColumn : S.vertex (w.target i) ⟶ S.vertex q :=
  eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hd i hp hq])) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S i.succ q (by change i.val + 1 ≤ q.val; omega)
      (fun j hj hj' => hd j (by change i.val + 1 ≤ j.val at hj; omega) hj')

lemma map_column_factorization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd =
      toColumn S p q hd i hp hq ≫ S.arrow i ≫ fromColumn S p q hd i hp hq := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_map_split_column S p q hpq hd i hp hq]
  simp only [toColumn, fromColumn, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow, Category.assoc]

lemma toColumn_mem (V : MorphismProperty C) [V.IsMultiplicative]
    (hV : ∀ j : Fin w.length, p.val ≤ j.val → j.val < i.val → V (S.arrow j)) :
    V (toColumn S p q hd i hp hq) := by
  apply V.comp_mem
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_map_mem S p i.castSucc hp _ V hV
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.eqToHom_mem _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
