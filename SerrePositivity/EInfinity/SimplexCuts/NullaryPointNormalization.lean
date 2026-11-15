module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInverse
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionNondegenerate

/-!
# 元の一点削除の前後の正規化零項の同値

Berger–Fresse §2.2.6、M14 L12a、報告 §334。
同じ水平境界の全削除座標へpairの単射性の法則を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 一点削除の前後で元の退化零項を含めて比較する（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_nondegenerate_iff {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2)) (hpoint : hi s p = lo s p)
    (hu : ∀ j, v j = v p → j = p) :
    Nondegenerate (nullaryPointEraseCut s p) (Surjection.erase v p) ↔ Nondegenerate s v := by
  obtain ⟨t, ht⟩ := nullaryPointInsertCut_surjective s p hpoint
  rw [← ht, nullaryPointEraseCut_insert, nullaryPointInsertCut_eq_horizontalBoundaryFace]
  let z := horizontalBoundaryFaceEquiv m q (p, t)
  exact nondegenerate_iff_horizontal_deleted_coordinates z.val.1 t v z.val.2 p
    (horizontalBoundaryFaceEquiv_horizontal m q (p, t))
    (fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).1)
    (fun j => (horizontalBoundaryFaceEquiv_deleted_coordinates m q (p, t) j).2) hu

end SerrePositivity.EInfinity.SimplexCuts
