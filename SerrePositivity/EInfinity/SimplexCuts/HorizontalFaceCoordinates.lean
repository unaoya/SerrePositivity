module

public import SerrePositivity.EInfinity.SimplexCuts.EndpointCoefficientIndices

/-!
# 全水平境界の同値が選ぶ元の区間番号

Berger–Fresse §2.2.7、M14 L09a。
既存の水平辺の昇順の番号と角への挿入の座標公式を、三分割へ貼り合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C217：既存の内部面の同値は、指定された内部の区間番号を水平座標に持つ。 -/
lemma horizontalInteriorFaceEquiv_horizontal (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalInteriorFaceEquiv m q (t, i)).val.1.horizontal
      (horizontalInteriorFaceEquiv m q (t, i)).val.2 = i.castSucc.succ := by
  apply Fin.ext
  change ((BarrattEccles.horizontalCornerEquiv m q
    (BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i))).val.1.horizontal
      (Fin.cast (by omega : m + q + 1 = m + 1 + q)
        (BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i)).val.2.castSucc).succ).val = i.val + 1
  exact (BarrattEccles.horizontalCornerEquiv_horizontal
    (BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i))).trans
      (congrArg (fun n : ℕ => n + 1) (BarrattEccles.horizontalMarkedEdgeEquiv_horizontal t i))

/-- C218：全水平境界の同値は、削除する元の文字の位置を保つ。 -/
lemma horizontalBoundaryFaceEquiv_horizontal (m q : ℕ) (c : Fin (m + 2) × Cut m q) :
    (horizontalBoundaryFaceEquiv m q c).val.1.horizontal
      (horizontalBoundaryFaceEquiv m q c).val.2 = c.1 := by
  obtain ⟨z, rfl⟩ := (coefficientIndexEndpointEquiv m q).symm.surjective c
  rcases z with t | ⟨t, i⟩ | t
  · rw [coefficientIndexEndpointEquiv_symm_first, horizontalBoundaryFaceEquiv_first]
    exact (horizontalFirstFaceEquiv m q t).val.1.horizontal_endpoints.1
  · rw [coefficientIndexEndpointEquiv_symm_interior, horizontalBoundaryFaceEquiv_interior]
    exact horizontalInteriorFaceEquiv_horizontal m q t i
  · rw [coefficientIndexEndpointEquiv_symm_last, horizontalBoundaryFaceEquiv_last]
    exact (horizontalLastFaceEquiv m q t).val.1.horizontal_endpoints.2

end SerrePositivity.EInfinity.SimplexCuts
