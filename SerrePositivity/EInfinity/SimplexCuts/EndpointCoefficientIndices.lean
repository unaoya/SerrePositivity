module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundaryEquiv

/-!
# 係数の全添字と水平端点の三分割の評価

Berger–Fresse §2.2.7、M14 L09a。
既存の添字の同値の逆を三つの枝で評価し、元の水平境界の同値へ戻す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C211：始端の枝は、元の係数語の最初の文字に戻る。 -/
lemma coefficientIndexEndpointEquiv_symm_first (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inl t) = (0, t) := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · rfl

/-- C212：内部の枝は、元の係数語の内部の文字に戻る。 -/
lemma coefficientIndexEndpointEquiv_symm_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inl (t, i))) = (i.castSucc.succ, t) := by
  apply Prod.ext
  · apply Fin.ext
    change 1 + i.val = i.val + 1
    omega
  · rfl

/-- C213：終端の枝は、元の係数語の最後の文字に戻る。 -/
lemma coefficientIndexEndpointEquiv_symm_last (m q : ℕ) (t : Cut m q) :
    (coefficientIndexEndpointEquiv m q).symm (.inr (.inr t)) = (Fin.last (m + 1), t) := by
  apply Prod.ext
  · apply Fin.ext
    change 1 + m = m + 1
    omega
  · rfl

/-- C214：全水平境界の始端の枝は、既存の水平始端挿入と同じ指定頂点。 -/
lemma horizontalBoundaryFaceEquiv_first (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (0, t)).val = (horizontalFirstFaceEquiv m q t).val := by
  rw [← coefficientIndexEndpointEquiv_symm_first m q t, horizontalBoundaryFaceEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- C215：全水平境界の内部の枝は、既存の水平角挿入と同じ指定頂点。 -/
lemma horizontalBoundaryFaceEquiv_interior (m q : ℕ) (t : Cut m q) (i : Fin m) :
    (horizontalBoundaryFaceEquiv m q (i.castSucc.succ, t)).val =
      (horizontalInteriorFaceEquiv m q (t, i)).val := by
  rw [← coefficientIndexEndpointEquiv_symm_interior m q t i, horizontalBoundaryFaceEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- C216：全水平境界の終端の枝は、既存の水平終端挿入と同じ指定頂点。 -/
lemma horizontalBoundaryFaceEquiv_last (m q : ℕ) (t : Cut m q) :
    (horizontalBoundaryFaceEquiv m q (Fin.last (m + 1), t)).val =
      (horizontalLastFaceEquiv m q t).val := by
  rw [← coefficientIndexEndpointEquiv_symm_last m q t, horizontalBoundaryFaceEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.EInfinity.SimplexCuts
