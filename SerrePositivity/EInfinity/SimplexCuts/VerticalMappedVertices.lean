module

public import SerrePositivity.EInfinity.SimplexCuts.StraightTraceFaces
public import SerrePositivity.EInfinity.SimplexCuts.DeletedVertices

/-!
# 垂直削除の色列と入力面の像

Berger–Fresse §2.2.6–7、M14 L09a。
既存の垂直削除の座標を各色の列へ写す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C242：同じ削除座標の下で、各色の列は入力面の頂点写像による像。 -/
lemma deletedVerticesList_vertical_of_coordinates {m q r : ℕ}
    (s : Cut m (q + 1)) (t : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) (c : Fin r) :
    deletedVerticesList s v k c =
      (verticesList t v c).map (s.vertical k).succAbove := by
  rw [deletedVerticesList_eq_selectColor, verticesList_eq_selectColor]
  have ht : deletedTrace s v k =
      (List.ofFn (fun j : Fin (m + q + 1) => (v (t.horizontal j), t.vertical j))).map
        (fun x => (x.1, (s.vertical k).succAbove x.2)) := by
    rw [List.map_ofFn]
    unfold deletedTrace label
    apply congrArg List.ofFn
    funext j
    exact Prod.ext (congrArg v (hh j)) (hv j)
  rw [ht, selectColor_map]

/-- C243：既存の内部の垂直挿入の逆で選んだ小さい切断に、同じ列の式を適用。 -/
lemma deletedVerticesList_vertical_interior {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val) (c : Fin r) :
    deletedVerticesList s v a.succ c =
      (verticesList ((BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (s.vertical a.succ).succAbove := by
  apply deletedVerticesList_vertical_of_coordinates
  · intro j
    exact BarrattEccles.verticalDeletion_horizontal s a ha j
  · intro j
    exact BarrattEccles.verticalDeletion_vertical s a b hab ha hb j

end SerrePositivity.EInfinity.SimplexCuts
