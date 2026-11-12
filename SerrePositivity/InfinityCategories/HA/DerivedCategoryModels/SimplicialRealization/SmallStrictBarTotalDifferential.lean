module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain

/-!
# shifted bar 列の微分の一点評価

## 概要
比較に使う同じ列の微分を、シフト前の同じ cochain の微分へ戻す。

## 方針
全 Hom の評価が鎖写像であることと、符号を変えないシフトの微分公式を使う。

## 規約
同じ列と同じ微分を保持し、閉性の仮定は加えない。

## 使われ方
HA 1.2.4。既存 theta に対する比較射の閉性の左辺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 同じ列の微分は、元のシフト前の微分を符号を変えずにshiftしたもの。 -/
theorem smallStrictBarTotalColumn_point_d (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F) PUnit.unit).f 1
      ((moduleHom A PUnit.{1}
        (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
        (smallStrictBarTotalTarget A F)).d 0 1 (smallStrictBarTotalColumn A F s)) =
      unsignedLeftShift
        (δ (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1) (smallStrictBarUnshiftedColumn A F s))
        (s.1 : ℤ) 1 (by omega) := by
  let f := moduleHomπ A PUnit.{1}
    (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
    (smallStrictBarTotalTarget A F) PUnit.unit
  have h := ConcreteCategory.congr_hom (f.comm 0 1).symm (smallStrictBarTotalColumn A F s)
  change f.f 1 _ = δ 0 1 (f.f 0 (smallStrictBarTotalColumn A F s)) at h
  apply h.trans
  exact congrArg (δ 0 1) (smallStrictBarTotalColumn_point A F s) |>.trans
    (unsignedLeftShift_δ _ _ _ _ _ _ (by omega))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
