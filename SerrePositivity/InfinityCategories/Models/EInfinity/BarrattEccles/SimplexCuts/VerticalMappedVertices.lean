module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.StraightTraceFaces
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedVertices

/-!
模型。文献の定義との比較は後で
# 垂直削除の色列と入力面の像

Berger–Fresse §2.2.6–7、M14 L09a。
既存の垂直削除の座標を各色の列へ写す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C242：同じ削除座標の下で、各色の列は入力面の頂点写像による像。 -/
lemma deletedVerticesList_vertical_of_coordinates {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + (q + 1) + 1))
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j)) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v k c =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t v c).map (s.vertical k).succAbove := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_eq_selectColor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_eq_selectColor]
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace s v k =
      (List.ofFn (fun j : Fin (m + q + 1) => (v (t.horizontal j), t.vertical j))).map
        (fun x => (x.1, (s.vertical k).succAbove x.2)) := by
    rw [List.map_ofFn]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label
    apply congrArg List.ofFn
    funext j
    exact Prod.ext (congrArg v (hh j)) (hv j)
  rw [ht, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_map]

/-- C243：既存の内部の垂直挿入の逆で選んだ小さい切断に、同じ列の式を適用。 -/
lemma deletedVerticesList_vertical_interior {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + (q + 1)))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∉ s.val) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v a.succ c =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList ((_root_.SerrePositivity.EInfinity.BarrattEccles.verticalInsertionEquiv m q a).symm ⟨s, ha⟩) v c).map
        (s.vertical a.succ).succAbove := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_vertical_of_coordinates
  · intro j
    exact _root_.SerrePositivity.EInfinity.BarrattEccles.verticalDeletion_horizontal s a ha j
  · intro j
    exact _root_.SerrePositivity.EInfinity.BarrattEccles.verticalDeletion_vertical s a b hab ha hb j

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
