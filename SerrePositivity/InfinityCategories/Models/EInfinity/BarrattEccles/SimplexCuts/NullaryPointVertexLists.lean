module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointInverse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionCoordinates

/-!
模型。文献の定義との比較は後で
# nullaryの一頂点削除の前後で残る元の頂点列

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §324。
元の全頂点列・同じ水平境界の削除座標・退化零項を保って比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 残る色の元の頂点列は、一頂点挿入の前後で厳密に同じ（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_verticesList_remaining {m q r : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (p : Fin (m + 2)) (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p) c = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut t p) v c := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_eq_horizontalBoundaryFace]
  let z := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv m q (p, t)
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace_eq_of_horizontal_coordinates z.val.1 t v z.val.2 p
    (fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).1)
    (fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).2)
  have hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label z.val.1 v z.val.2 ≠ c := by
    intro h
    change v (z.val.1.horizontal z.val.2) = c at h
    have hz := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_horizontal m q (p, t)
    change z.val.1.horizontal z.val.2 = p at hz
    rw [hz] at h
    exact hc h
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (List.ofFn (fun j : Fin (m + q + 1) =>
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p (t.horizontal j), t.vertical j))) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_eq_selectColor t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p) c
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace z.val.1 v z.val.2) := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c) ht.symm
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList z.val.1 v z.val.2 c :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_eq_selectColor z.val.1 v z.val.2 c).symm
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList, ite_eq_right hn]

/-- 元の一頂点を削除しても、削除しない色の全頂点列は変わらない（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_verticesList_remaining {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (p : Fin (m + 2)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p)
    (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p) c = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s v c := by
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_surjective s p h
  rw [← ht, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_insert]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_verticesList_remaining t p v c hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
