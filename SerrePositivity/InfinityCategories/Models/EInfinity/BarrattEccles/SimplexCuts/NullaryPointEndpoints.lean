module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointInverse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionMinima

/-!
模型。文献の定義との比較は後で
# 一点削除の前後の全区間の両端

Berger–Fresse §2.2.6、M14 L12a、報告 §326。
元の水平境界の指定座標を使い、残る区間の両端を厳密に比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 一点削除は残る元の全区間の両端を保つ（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_endpoints {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (p : Fin (m + 2))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s (p.succAbove i) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (p.succAbove i) := by
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_surjective s p h
  rw [← ht, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_insert, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_eq_horizontalBoundaryFace]
  let z := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv m q (p, t)
  have hk : z.val.1.horizontal z.val.2 = p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_horizontal m q (p, t)
  have hh := fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).1
  have hv := fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).2
  exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_eq_of_horizontal_deleted_coordinates z.val.1 t z.val.2 p hk hh hv i,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_horizontal_deleted_coordinates z.val.1 t z.val.2 p hk hh hv i⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
