module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgewiseRefinementVertex

/-!
概要：元の一単体を保持する共通解像の頂点の両射影は元の二端点。
方針：零次元の重みの左右包含を標準一単体の二面へ戻す。
規約：元の一単体と反転を保持する。
使われ方：左右区間比較の指定成分の端点を元の精密化の両端へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 共通解像の元の実頂点の右射影は元の一単体の終点。 -/
lemma edgewiseRefinementVertex_right {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseRight X).app (Opposite.op ⦋0⦌) (edgewiseRefinementVertex e) = X.δ 0 e := by
  change SSet.yonedaEquiv (joinInr _ _ ≫ (edgewiseWeightIso 0).hom ≫
    SSet.yonedaEquiv.symm e) = _
  have h : SimplexCategory.mkHom (DGNerve.joinRightOrderHom 0 0) =
      SimplexCategory.δ (0 : Fin 2) := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInr _ _), edgewiseWeightIso_inr, h,
    ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  rfl

/-- 共通解像の元の実頂点の左射影は元の一単体の始点の反転。 -/
lemma edgewiseRefinementVertex_left {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseLeft X).app (Opposite.op ⦋0⦌) (edgewiseRefinementVertex e) =
      SSet.opObjEquiv.symm (X.δ 1 e) := by
  change SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso ⦋0⦌).inv ≫
    joinInl _ _ ≫ (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm e)) = _
  apply congrArg SSet.opObjEquiv.symm
  have h : SimplexCategory.mkHom (DGNerve.joinLeftOrderHom 0 0) =
      SimplexCategory.δ (1 : Fin 2) := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInl _ _), edgewiseWeightIso_inl, Category.assoc,
    Iso.inv_hom_id_assoc, h, ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.F2
