module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalMappedVertices
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLastFace

/-!
# 垂直端点を削除した色列

Berger–Fresse §2.2.6–7、M14 L09a。
既存の始端・終端の削除座標を、同じ入力面による像の色列へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C244：垂直始端の削除色列は、零番目の入力面による像。 -/
lemma deletedVerticesList_vertical_first {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (h₀ : (0 : Fin (m + (q + 1))) ∉ s.val) (c : Fin r) :
    deletedVerticesList s v 0 c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q 0).symm ⟨s, h₀⟩) v c).map
        (0 : Fin (q + 2)).succAbove := by
  have ht := deletedVerticesList_vertical_of_coordinates s
    ((BarrattEccles.verticalInsertionEquiv m q 0).symm ⟨s, h₀⟩) v 0
    (by intro j; simpa only [Fin.succAbove_zero] using
      BarrattEccles.verticalDeletion_first_horizontal s h₀ j)
    (by intro j; simpa only [s.vertical_endpoints.1, Fin.succAbove_zero] using
      BarrattEccles.verticalDeletion_first_vertical s h₀ j) c
  simpa only [s.vertical_endpoints.1] using ht

/-- C245：垂直終端の削除色列は、最後の入力面による像。 -/
lemma deletedVerticesList_vertical_last {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a : Fin (m + (q + 1))) (ha : a ∉ s.val)
    (hlast : a.val + 1 = m + (q + 1)) (c : Fin r) :
    deletedVerticesList s v (Fin.last (m + (q + 1))) c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (Fin.last (q + 1)).succAbove := by
  have hk : a.succ = Fin.last (m + (q + 1)) := Fin.ext hlast
  have ht := deletedVerticesList_vertical_of_coordinates s
    ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v a.succ
    (BarrattEccles.verticalDeletion_horizontal s a ha)
    (by intro j; rw [hk, s.vertical_endpoints.2];
        simpa only [hk] using BarrattEccles.verticalDeletion_last s a ha hlast j) c
  simpa only [hk, s.vertical_endpoints.2] using ht

end SerrePositivity.EInfinity.SimplexCuts
