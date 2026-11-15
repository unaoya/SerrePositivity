module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInverse
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionCoordinates

/-!
# nullaryの一頂点削除の前後で残る元の頂点列

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §324。
元の全頂点列・同じ水平境界の削除座標・退化零項を保って比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 残る色の元の頂点列は、一頂点挿入の前後で厳密に同じ（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_verticesList_remaining {m q r : ℕ} (t : Cut m q)
    (p : Fin (m + 2)) (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    verticesList t (Surjection.erase v p) c = verticesList (nullaryPointInsertCut t p) v c := by
  rw [nullaryPointInsertCut_eq_horizontalBoundaryFace]
  let z := horizontalBoundaryFaceEquiv m q (p, t)
  have ht := deletedTrace_eq_of_horizontal_coordinates z.val.1 t v z.val.2 p
    (fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).1)
    (fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).2)
  have hn : label z.val.1 v z.val.2 ≠ c := by
    intro h
    change v (z.val.1.horizontal z.val.2) = c at h
    have hz := horizontalBoundaryFaceEquiv_horizontal m q (p, t)
    change z.val.1.horizontal z.val.2 = p at hz
    rw [hz] at h
    exact hc h
  calc
    _ = selectColor c (List.ofFn (fun j : Fin (m + q + 1) =>
        (Surjection.erase v p (t.horizontal j), t.vertical j))) :=
      verticesList_eq_selectColor t (Surjection.erase v p) c
    _ = selectColor c (deletedTrace z.val.1 v z.val.2) := congrArg (selectColor c) ht.symm
    _ = deletedVerticesList z.val.1 v z.val.2 c :=
      (deletedVerticesList_eq_selectColor z.val.1 v z.val.2 c).symm
    _ = _ := by rw [deletedVerticesList, ite_eq_right hn]

/-- 元の一頂点を削除しても、削除しない色の全頂点列は変わらない（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_verticesList_remaining {m q r : ℕ} (s : Cut (m + 1) q)
    (p : Fin (m + 2)) (h : hi s p = lo s p)
    (v : Fin (m + 2) → Fin r) (c : Fin r) (hc : v p ≠ c) :
    verticesList (nullaryPointEraseCut s p) (Surjection.erase v p) c = verticesList s v c := by
  obtain ⟨t, ht⟩ := nullaryPointInsertCut_surjective s p h
  rw [← ht, nullaryPointEraseCut_insert]
  exact nullaryPointInsertCut_verticesList_remaining t p v c hc

end SerrePositivity.EInfinity.SimplexCuts
