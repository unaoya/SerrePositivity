module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInverse
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionMinima

/-!
# 一点削除の前後の全区間の両端

Berger–Fresse §2.2.6、M14 L12a、報告 §326。
元の水平境界の指定座標を使い、残る区間の両端を厳密に比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 一点削除は残る元の全区間の両端を保つ（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_endpoints {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) (i : Fin (m + 1)) :
    lo (nullaryPointEraseCut s p) i = lo s (p.succAbove i) ∧
      hi (nullaryPointEraseCut s p) i = hi s (p.succAbove i) := by
  obtain ⟨t, ht⟩ := nullaryPointInsertCut_surjective s p h
  rw [← ht, nullaryPointEraseCut_insert, nullaryPointInsertCut_eq_horizontalBoundaryFace]
  let z := horizontalBoundaryFaceEquiv m q (p, t)
  have hk : z.val.1.horizontal z.val.2 = p := horizontalBoundaryFaceEquiv_horizontal m q (p, t)
  have hh := fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).1
  have hv := fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).2
  exact ⟨lo_eq_of_horizontal_deleted_coordinates z.val.1 t z.val.2 p hk hh hv i,
    hi_eq_of_horizontal_deleted_coordinates z.val.1 t z.val.2 p hk hh hv i⟩

end SerrePositivity.EInfinity.SimplexCuts
