module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedVertices
public import SerrePositivity.EInfinity.Surjection.Deletion
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
# 同方向の二辺の中間頂点を除いた列

Berger–Fresse §2.2.7、M14 L09a。
既存の水平・垂直の削除座標公式を、同じ色付き頂点列へ戻す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C89：内部の水平面は係数語の一文字を消した小さい切断の列。 -/
lemma horizontal_deletedTrace {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) :
    deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
      (Surjection.erase v (s.horizontal a.succ)
        (((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
      ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k)) := by
  unfold deletedTrace
  rw [List.ofFn_congr (show m + 1 + q = m + q + 1 by omega)]
  apply congrArg List.ofFn
  funext k
  have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k) = k := Fin.ext rfl
  apply Prod.ext
  · change v (s.horizontal (a.succ.succAbove (Fin.cast _ k))) =
      v ((s.horizontal a.succ).succAbove
        (((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k))
    apply congrArg v
    have hh := BarrattEccles.horizontalDeletion_horizontal s a b hab ha hb
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    rw [hc] at hh
    exact hh
  · have hv := BarrattEccles.horizontalDeletion_vertical s a ha
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    rw [hc] at hv
    exact hv

/-- C90：内部の垂直面は入力頂点を一つ飛ばす小さい切断の列。 -/
lemma vertical_deletedTrace {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1))) (hab : b.val = a.val + 1)
    (ha : a ∉ s.val) (hb : b ∉ s.val) :
    deletedTrace s v a.succ = List.ofFn (fun k : Fin (m + q + 1) =>
      (v (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).horizontal k),
      (s.vertical a.succ).succAbove
        (((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩).vertical k))) := by
  unfold deletedTrace
  apply congrArg List.ofFn
  funext k
  apply Prod.ext
  · exact congrArg v (BarrattEccles.verticalDeletion_horizontal s a ha k)
  · exact BarrattEccles.verticalDeletion_vertical s a b hab ha hb k

end SerrePositivity.EInfinity.SimplexCuts
