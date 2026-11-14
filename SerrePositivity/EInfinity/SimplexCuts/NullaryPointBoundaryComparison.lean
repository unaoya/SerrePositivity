module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInsertionValues
public import SerrePositivity.EInfinity.SimplexCuts.AdjacentHorizontalInsertions
public import SerrePositivity.EInfinity.SimplexCuts.AllHorizontalDeletionCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalSingletons

/-!
# 元のnullary挿入と同じ水平境界のCutの厳密な一致

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の既存構成の法則、報告 §318・§320。
内部の前後挿入も同じ辺集合へ合わせ、元の指定区間を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元のnullary挿入は、既存の全水平境界の同じCut（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_eq_horizontalBoundaryFace {m q : ℕ}
    (t : Cut m q) (p : Fin (m + 2)) :
    nullaryPointInsertCut t p = (horizontalBoundaryFaceEquiv m q (p, t)).val.1 := by
  by_cases hzero : p.val = 0
  · have hp : p = 0 := Fin.ext hzero
    subst p
    rw [horizontalBoundaryFaceEquiv_first]
    rfl
  by_cases hlast : p.val = m + 1
  · have hp : p = Fin.last (m + 1) := Fin.ext hlast
    subst p
    rw [horizontalBoundaryFaceEquiv_last]
    unfold nullaryPointInsertCut
    rw [nullaryPointInsertionEdge_last]
    rfl
  let i : Fin m := ⟨p.val - 1, by have hp := p.isLt; omega⟩
  have hp : p = i.castSucc.succ := by
    apply Fin.ext
    change p.val = (p.val - 1) + 1
    omega
  rw [hp, horizontalBoundaryFaceEquiv_interior]
  unfold nullaryPointInsertCut
  rw [nullaryPointInsertionEdge_interior]
  change (BarrattEccles.horizontalInsertionEquiv m q
      (Fin.cast (by omega) (cutHorizontalEdge t i).succ) t).val =
    (BarrattEccles.horizontalInsertionEquiv m q
      (Fin.cast (by omega) (cutHorizontalEdge t i).castSucc) t).val
  exact (horizontalInsertionEquiv_adjacent_of_mem t (cutHorizontalEdge t i)
    (t.val.orderEmbOfFin_mem t.property i)).symm

/-- 全水平境界の指定区間は同じ一頂点（BF §2.2.6）。 -/
lemma horizontalBoundaryFaceEquiv_hi_eq_lo (m q : ℕ) (p : Fin (m + 2)) (t : Cut m q) :
    hi (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p =
      lo (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p := by
  have h := ((boundaryVertexKind_eq_horizontal_gap
    (horizontalBoundaryFaceEquiv m q (p, t)).val.1
    (horizontalBoundaryFaceEquiv m q (p, t)).val.2).mp
      (horizontalBoundaryFaceEquiv m q (p, t)).property).2
  rw [horizontalBoundaryFaceEquiv_horizontal] at h
  change hi (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p -
    lo (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p = 0 at h
  have hl := lo_le_hi (horizontalBoundaryFaceEquiv m q (p, t)).val.1 p
  omega

/-- 元のnullary挿入で指定した区間の両端は同じ（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_hi_eq_lo {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    hi (nullaryPointInsertCut t p) p = lo (nullaryPointInsertCut t p) p := by
  rw [nullaryPointInsertCut_eq_horizontalBoundaryFace]
  exact horizontalBoundaryFaceEquiv_hi_eq_lo m q p t

end SerrePositivity.EInfinity.SimplexCuts
