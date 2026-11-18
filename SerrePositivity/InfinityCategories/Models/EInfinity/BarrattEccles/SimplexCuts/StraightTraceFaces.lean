module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
模型。文献の定義との比較は後で
# 同方向の二辺の中間頂点を除いた列

Berger–Fresse §2.2.7、M14 L09a。
既存の水平・垂直の削除座標公式を、同じ色付き頂点列へ戻す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C89：内部の水平面は係数語の一文字を消した小さい切断の列。 -/
lemma horizontal_deletedTrace {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v (s.horizontal a.succ)
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace
  rw [List.ofFn_congr (show m + 1 + q = m + q + 1 by omega)]
  apply congrArg List.ofFn
  funext k
  have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k) = k := Fin.ext rfl
  apply Prod.ext
  · change v (s.horizontal (a.succ.succAbove (Fin.cast _ k))) =
      v ((s.horizontal a.succ).succAbove
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k))
    apply congrArg v
    have hh := _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_horizontal s a b hab ha hb
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    rw [hc] at hh
    exact hh
  · have hv := _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_vertical s a ha
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    rw [hc] at hv
    exact hv

/-- C90：内部の垂直面は入力頂点を一つ飛ばす小さい切断の列。 -/
lemma vertical_deletedTrace {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
      (v (((_root_.SerrePositivity.EInfinity.BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
      (s.vertical a.succ).succAbove
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace
  apply congrArg List.ofFn
  funext k
  apply Prod.ext
  · exact congrArg v (_root_.SerrePositivity.EInfinity.BarrattEccles.verticalDeletion_horizontal s a ha k)
  · exact _root_.SerrePositivity.EInfinity.BarrattEccles.verticalDeletion_vertical s a b hab ha hb k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
