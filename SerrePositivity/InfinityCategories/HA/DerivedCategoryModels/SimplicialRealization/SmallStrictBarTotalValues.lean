module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
public import SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain
import all SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison

/-!
# 同じ strict bar の列の一点評価

## 概要
既存の全 Hom の同型を戻して作った列を、元の直和全複体の同じ包含として計算する。

## 方針
一点 Hom の同型の逆を打ち消し、符号を変えない始域のシフトの成分公式を使う。

## 規約
元の射列と単体的置換の余積包含を保つ。

## 使われ方
HA 1.2.4。既存 theta に対する閉性の成分計算と標準脚の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance smallStrictBarTotalValues_hasCoproducts : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 同じ射列の先頭の値から、置換の実現へのシフト前の標準列。 -/
def smallStrictBarUnshiftedColumn (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    Cochain ((smallStrictBarCoefficientDiagram A F).obj (s.2.down.obj 0))
      ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) (-(s.1 : ℤ)) :=
  (Cochain.ofHom (Sigma.ι
    (replacementTerms (smallStrictBarCoefficientDiagram A F) (op ⦋s.1⦌)) s.2.down)).comp
      (standardRowCochain A (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) s.1)
      (zero_add _)

/-- 一点 Hom の評価は、元のシフト前の列の符号を変えないシフトである。 -/
theorem smallStrictBarTotalColumn_point (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s) =
      unsignedLeftShift (smallStrictBarUnshiftedColumn A F s) (s.1 : ℤ) 0 (by omega) := by
  let M := ForgetEnrichment.to (Complex A)
    (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s)
  let e := ringModuleHomIso A M (smallStrictBarTotalTarget A F)
  let w := (((s.1 : ℤ) * ((s.1 : ℤ) - 1)) / 2).negOnePow •
    (smallStrictBarUnshiftedColumn A F s).leftShift (s.1 : ℤ) 0 (by omega)
  dsimp only [unsignedLeftShift]
  simp only [mul_zero, zero_add]
  change e.hom.f 0 (e.inv.f 0 w) = w
  exact ConcreteCategory.congr_hom
    (((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) 0).mapIso e).inv_hom_id) w

/-- シフト前の同じ列の各成分は、射列の因子の包含の後の同じ行の包含。 -/
theorem smallStrictBarUnshiftedColumn_v (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (p q : ℤ) (h : p + -(s.1 : ℤ) = q) :
    (smallStrictBarUnshiftedColumn A F s).v p q h =
      (Sigma.ι (replacementTerms (smallStrictBarCoefficientDiagram A F) (op ⦋s.1⦌)) s.2.down).f p ≫
        (standardRowCochain A (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) s.1).v
          p q h := by
  exact Cochain.comp_v _ _ (zero_add _) p p q (by omega) h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
