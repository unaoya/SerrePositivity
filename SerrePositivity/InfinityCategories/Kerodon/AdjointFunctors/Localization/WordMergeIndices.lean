module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMerge
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Lean.Elab.Tactic.Omega

/-!
# 元の二重隣接合成の位置と色の比較

概要：二つの合成位置を入れ替えても、残る二列を同じ向きで合成できる。
方針：元の列の像を Fin.predAbove で計算し、語の色保存を使う。
規約：接する二つの合成位置も含み、元の二重全射を同定する。
使われ方：合成同士の元の基本縮約の局所合流。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma direction_eq_of_images {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i j : Fin a.length)
    (p q : Fin b.length) (hi : f.orderHom i = p) (hj : f.orderHom j = q)
    (h : a.direction i = a.direction j) : b.direction p = b.direction q :=
  ((congrArg b.direction hi).symm.trans (f.direction_eq i)).trans
    (h.trans ((f.direction_eq j).symm.trans (congrArg b.direction hj)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (direction_eq_of_images)


variable {k : ℕ} (d : Fin (k + 3) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i j : Fin (k + 1)) (hij : i ≤ j)
include hij

lemma merge_left_remaining_color
    (hi : d i.castSucc.castSucc = d i.castSucc.succ)
    (hj : d j.succ.castSucc = d j.succ.succ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d i.castSucc).direction j.castSucc =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d i.castSucc).direction j.succ := by
  have hL : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d i.castSucc hi).orderHom j.succ.castSucc = j.castSucc := by
    change i.castSucc.predAbove j.succ.castSucc = j.castSucc
    rw [Fin.castSucc_predAbove_castSucc, Fin.predAbove_succ_of_le _ _ hij]
  have hR : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d i.castSucc hi).orderHom j.succ.succ = j.succ := by
    change i.castSucc.predAbove j.succ.succ = j.succ
    apply Fin.predAbove_succ_of_le
    change i.val ≤ j.val + 1
    have h : i.val ≤ j.val := hij
    omega
  exact direction_eq_of_images (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d i.castSucc hi) _ _ _ _ hL hR hj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (merge_left_remaining_color)


lemma merge_right_remaining_color
    (hi : d i.castSucc.castSucc = d i.castSucc.succ)
    (hj : d j.succ.castSucc = d j.succ.succ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d j.succ).direction i.castSucc =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d j.succ).direction i.succ := by
  have hL : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d j.succ hj).orderHom i.castSucc.castSucc = i.castSucc := by
    change j.succ.predAbove i.castSucc.castSucc = i.castSucc
    apply Fin.predAbove_castSucc_of_le
    change i.val ≤ j.val + 1
    have h : i.val ≤ j.val := hij
    omega
  have hR : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d j.succ hj).orderHom i.castSucc.succ = i.succ := by
    change j.succ.predAbove i.castSucc.succ = i.succ
    rw [Fin.predAbove_of_le_castSucc _ _ (by
      change i.val + 1 ≤ j.val + 1
      exact Nat.add_le_add_right hij 1)]
    exact Fin.ext rfl
  exact direction_eq_of_images (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d j.succ hj) _ _ _ _ hL hR hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (merge_right_remaining_color)


/-- 単体圏の元の合成則による、同じ元の二重全射の一致。 -/
lemma merge_predAbove_comp (x : Fin (k + 3)) :
    j.predAbove (i.castSucc.predAbove x) = i.predAbove (j.succ.predAbove x) := by
  exact congrArg (fun f : SimplexCategory.mk (k + 2) ⟶ SimplexCategory.mk k => f.toOrderHom x)
    (SimplexCategory.σ_comp_σ hij)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (merge_predAbove_comp)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
