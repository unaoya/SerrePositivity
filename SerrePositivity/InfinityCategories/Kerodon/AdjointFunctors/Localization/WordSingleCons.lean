module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCons
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit

/-!
# 元の一列の連結と先頭追加の一致

概要：元の一列の語の連結は同じ向きの先頭追加に厳密に一致する。
方針：元の列番号を長さの等式で移して先頭と残りに分ける。
規約：両方向と空語を含む。
使われ方：DK5.7の元の連結表示を長さ帰納の表示へ戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
lemma single_append_eq_cons (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d) w = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext _ _ (Nat.add_comm 1 w.length) ?_
  intro i
  change Fin (1 + w.length) at i
  cases i using Fin.addCases with
  | left i =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hidx : Fin.cast (Nat.add_comm 1 w.length) ((0 : Fin 1).castAdd w.length) =
        (0 : Fin (w.length + 1)) := by apply Fin.ext; rfl
    change d = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).direction _
    rw [hidx]
    rfl
  | right i =>
    refine (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d) w i).trans ?_
    have hidx : Fin.cast (Nat.add_comm 1 w.length) (i.natAdd 1) = i.succ := by
      apply Fin.ext
      change 1 + i.val = i.val + 1
      omega
    rw [hidx]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (single_append_eq_cons)

lemma cons_empty (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d := by
  rw [← single_append_eq_cons, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cons_empty)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
