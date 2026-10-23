module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgewiseRefinementResolutions

/-!
概要：元の精密化を保持する二つの共通解像の残りの射影は元の両端に定値。
方針：標準三単体の左右の包含と退化を有限順序の射として計算する。
規約：元の一単体と実共通解像の係数を保持する。
使われ方：共通解像上の自然性の二正方形で反転側と右側の精密化を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 右側の共通解像の左射影は元の一単体の始点へ定値。 -/
lemma edgewiseRefinementRightResolution_left {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseLeft X).app (Opposite.op ⦋1⦌) (edgewiseRefinementRightResolution e) =
      SSet.opObjEquiv.symm (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e) := by
  change SSet.opObjEquiv.symm (SSet.yonedaEquiv
    ((stdSimplex.opIso ⦋1⦌).inv ≫ joinInl _ _ ≫
    (edgewiseWeightIso 1).hom ≫
      stdSimplex.map (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) ≫
        SSet.yonedaEquiv.symm e)) =
      SSet.opObjEquiv.symm (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e)
  apply congrArg SSet.opObjEquiv.symm
  have h : SimplexCategory.mkHom (DGNerve.joinLeftOrderHom 1 1) ≫
      (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInl _ _), edgewiseWeightIso_inl, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc (stdSimplex.map _),
    ← stdSimplex.map_comp, h, ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- 左側の共通解像の右射影は元の一単体の終点へ定値。 -/
lemma edgewiseRefinementLeftResolution_right {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseRight X).app (Opposite.op ⦋1⦌) (edgewiseRefinementLeftResolution e) =
      X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e := by
  change SSet.yonedaEquiv (joinInr _ _ ≫ (edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) ≫
      SSet.yonedaEquiv.symm e) = _
  have h : SimplexCategory.mkHom (DGNerve.joinRightOrderHom 1 1) ≫
      (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInr _ _), edgewiseWeightIso_inr,
    ← Category.assoc (stdSimplex.map _), ← stdSimplex.map_comp, h,
    ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
