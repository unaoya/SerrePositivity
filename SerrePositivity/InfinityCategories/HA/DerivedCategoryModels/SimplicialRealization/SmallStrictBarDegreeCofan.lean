module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.RealizationDegreeCofan
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ShiftedCoproductDegreeCofan
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain

/-!
# 同じ比較列による実現の各次数の余積

## 概要
既に指定した比較の全ての列の各次数の成分が、標的の同じ余積の脚になる。

## 方針
行の余積と shifted 因子の余積の普遍性を合成し、元の列の成分公式で照合する。

## 規約
射列の ULift 添字と、比較の元の列を保つ。

## 使われ方
HA 1.2.4。smallStrictBarTotalHom の各次数での同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance smallStrictBarDegreeCofan_hasCoproducts : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の各比較列の同じ次数成分を脚に持つ余積候補。 -/
def smallStrictBarDegreeCofan (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    Cofan (fun s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) =>
      ((ForgetEnrichment.to (Complex A)
        (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s)).obj (op PUnit.unit)).X q) :=
  Cofan.mk (((smallStrictBarTotalTarget A F).obj (op PUnit.unit)).X q) (fun s =>
    ((moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s)).v q q (add_zero q))

/-- 同じ比較列の成分は、全次数で標的の余積を与える。 -/
def smallStrictBarDegreeCofan_isColimit (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    IsColimit (smallStrictBarDegreeCofan A F q) := by
  let X := smallStrictBarCoefficientDiagram A F
  let c := realizationDegreeCofan A (simplicialReplacement X) q
  let π := fun n : ℕ => shiftedCoproductDegreeCofan.{u, 0, u} A
    (replacementTerms X (op ⦋n⦌)) (n : ℤ) q
  have hc := Cofan.isColimitTrans c (realizationDegreeCofan_isColimit A _ q)
    (fun n s => (π n).inj s) (fun n => shiftedCoproductDegreeCofan_isColimit A _ (n : ℤ) q)
  apply IsColimit.ofIsoColimit hc
  refine Cofan.ext (Iso.refl _) ?_
  intro s
  change ((π s.1).inj s.2 ≫ c.inj s.1) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change (((X.obj (s.2.down.obj 0)).shiftFunctorObjXIso (s.1 : ℤ) q (q + (s.1 : ℤ)) rfl).hom ≫
    (Sigma.ι (replacementTerms X (op ⦋s.1⦌)) s.2.down).f (q + (s.1 : ℤ))) ≫
      (standardRowCochain A (simplicialReplacement X) s.1).v (q + (s.1 : ℤ)) q (by omega) = _
  change _ = ((moduleHomπ A PUnit.{1}
    (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
    (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalColumn A F s)).v q q (add_zero q)
  rw [smallStrictBarTotalColumn_point A F s, unsignedLeftShift_v,
    smallStrictBarUnshiftedColumn_v A F s, Category.assoc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
