module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomDegrees
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import SerrePositivity.HomologicalAlgebra.SimplicialReplacement
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# 同じ strict bar の各 shifted 因子から実現への成分

## 概要
射列の先頭の値を単体的置換の同じ因子に入れ、次数 -n の標準成分を shift して戻す。

## 方針
一点 dg 加群の全 Hom 評価同型と、既存 bar の graded 余積の Hom 同値を使う。

## 規約
shift の三角数の符号を打ち消し、各次数で元の直和包含を保持する。
このファイルではまだ Maurer–Cartan 微分に対する閉性を主張しない。

## 使われ方
HA 1.2.4。既存 native bar と単体的置換の直和全複体の実際の比較射の成分。
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

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の strict dg 加群図式の唯一の値を評価した、元の非有界複体図式。 -/
def smallStrictBarCoefficientDiagram (F : J ⥤ ModuleCategory A PUnit.{1}) : J ⥤ Complex A :=
  F ⋙ moduleEvaluation A PUnit.{1} PUnit.unit

/-- 同じ strict 射列の置換の直和全複体を、一点 dg 加群として読む。 -/
def smallStrictBarTotalTarget (F : J ⥤ ModuleCategory A PUnit.{1}) : RightModule A PUnit.{1} :=
  ringModule A ((directSumTotalFunctor A).obj (simplicialReplacement (smallStrictBarCoefficientDiagram A F)))

/-- 元の各射列の shifted 因子から、同じ直和全複体への次数零の成分。 -/
def smallStrictBarTotalColumn (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (moduleHom A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F)).X 0 := by
  let X := smallStrictBarCoefficientDiagram A F
  let z := (Cochain.ofHom (Sigma.ι (replacementTerms X (op ⦋s.1⦌)) s.2.down)).comp
    (standardRowCochain A (simplicialReplacement X) s.1) (zero_add _)
  let M := ForgetEnrichment.to (Complex A)
    (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s)
  let w : Cochain (M.obj (op PUnit.unit))
      ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) 0 :=
    (((s.1 : ℤ) * ((s.1 : ℤ) - 1)) / 2).negOnePow •
      z.leftShift (s.1 : ℤ) 0 (by omega)
  exact (ringModuleHomIso A M (smallStrictBarTotalTarget A F)).inv.f 0 w

/-- 同じ列族を、元の graded bar からの一つの次数零の Hom 要素にまとめる。 -/
def smallStrictBarTotalGradedElement (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (moduleHom A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
      (smallStrictBarTotalTarget A F)).X 0 :=
  (dgCoherentBarHomEquiv A PUnit.{1} (smallStrictBarDiagram A F)
    (ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F)) 0).symm
      (smallStrictBarTotalColumn A F)

/-- 各元の shifted 因子に制限すると、同じ指定した列が返る。 -/
theorem smallStrictBarTotalGradedElement_column (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    dgCoherentBarHomEquiv A PUnit.{1} (smallStrictBarDiagram A F)
      (ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F)) 0
      (smallStrictBarTotalGradedElement A F) s = smallStrictBarTotalColumn A F s :=
  congrFun ((dgCoherentBarHomEquiv A PUnit.{1} (smallStrictBarDiagram A F)
    (ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F)) 0).apply_symm_apply _) s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
