module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.EndpointCoefficientIndices

/-!
模型。文献の定義との比較は後で
# 全水平境界の同値が選ぶ元の区間番号

Berger–Fresse §2.2.7、M14 L09a。
既存の水平辺の昇順の番号と角への挿入の座標公式を、三分割へ貼り合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C217：既存の内部面の同値は、指定された内部の区間番号を水平座標に持つ。 -/
lemma horizontalInteriorFaceEquiv_horizontal (m q : ℕ) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalInteriorFaceEquiv m q (t, i)).val.1.horizontal
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalInteriorFaceEquiv m q (t, i)).val.2 = i.castSucc.succ := by
  apply Fin.ext
  change ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalCornerEquiv m q
    (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i))).val.1.horizontal
      (Fin.cast (by omega : m + q + 1 = m + 1 + q)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i)).val.2.castSucc).succ).val = i.val + 1
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalCornerEquiv_horizontal
    (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i))).trans
      (congrArg (fun n : ℕ => n + 1) (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalMarkedEdgeEquiv_horizontal t i))

/-- C218：全水平境界の同値は、削除する元の文字の位置を保つ。 -/
lemma horizontalBoundaryFaceEquiv_horizontal (m q : ℕ) (c : Fin (m + 2) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv m q c).val.1.horizontal
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv m q c).val.2 = c.1 := by
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientIndexEndpointEquiv m q).symm.surjective c
  rcases z with t | ⟨t, i⟩ | t
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientIndexEndpointEquiv_symm_first, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_first]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalFirstFaceEquiv m q t).val.1.horizontal_endpoints.1
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientIndexEndpointEquiv_symm_interior, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_interior]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalInteriorFaceEquiv_horizontal m q t i
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientIndexEndpointEquiv_symm_last, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv_last]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalLastFaceEquiv m q t).val.1.horizontal_endpoints.2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
