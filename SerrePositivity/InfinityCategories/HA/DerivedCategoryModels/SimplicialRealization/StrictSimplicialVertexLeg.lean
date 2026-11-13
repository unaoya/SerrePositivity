module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialBarRealization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.NativeVertexInclusion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarUnshiftedBoundary
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDegreeCofan

/-!
# 同じ native 頂点列と元の実現の標準脚

## 概要
補正包含・元の比較・増大の合成が、元の零行への標準脚そのものになる。
## 方針
零shiftの逆則を保ち、既存の各因子の比較と零行の自然性を用いる。
## 規約
射列の先頭の零頂点を使う。同じ複体の射の等式で述べる。
## 使われ方
HA 1.2.4、HTT 4.2.4.1。図式ごとの指定実現余錐の脚。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
variable (A : Type u) [CommRing A]

local instance strictSimplicialVertexLeg_hasCoproducts : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 同じ native 頂点列の正規化比較は、置換の同じ零行の標準包含。 -/
theorem smallStrictBarNormalizedTotalHom_vertex
    (F : SimplicialObject (ModuleCategory A PUnit.{1}))
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ)) _⦋0⦌) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map
      (dgBarNativeVertexModuleMap A PUnit.{1} (smallStrictBarDiagram A F) s ≫
        smallStrictBarNormalizedTotalHom A F) =
    Sigma.ι (replacementTerms (smallStrictBarCoefficientDiagram A F) (op ⦋0⦌)) s.down ≫
      standardZeroLeg A (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) := by
  apply HomologicalComplex.Hom.ext
  funext q
  rw [smallStrictBarNormalizedTotalHom, ← Category.assoc]
  rw [Functor.map_comp, HomologicalComplex.comp_f,
    dgBarNativeVertexModuleMap_inclusion_f A PUnit.{1} (smallStrictBarDiagram A F) s PUnit.unit q,
    Category.assoc, smallStrictBarTotalHom_point_ι A F q ⟨0, s⟩]
  change _ ≫ ((moduleHomπ A PUnit.{1} _ _ PUnit.unit).f 0
    (smallStrictBarTotalColumn A F ⟨0, s⟩)).v q q (add_zero q) = _
  rw [smallStrictBarTotalColumn_point]
  change _ ≫ (unsignedLeftShift (smallStrictBarUnshiftedColumn A F ⟨0, s⟩) 0 0 rfl).v
    q q (add_zero q) = _
  unfold unsignedLeftShift
  simp only [zero_mul, zero_add, zero_sub, Int.zero_ediv, Int.negOnePow_zero, one_smul]
  rw [Cochain.leftShift_v _ 0 0 rfl q q (add_zero q) q (add_zero q)]
  rw [moduleShiftZeroIsoObj_inv_eval, smallStrictBarUnshiftedColumn_v, standardRowCochain_zero]
  simp [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, Cochain.ofHom_v]

/-- 元の標準脚。先頭単体の零頂点から、元の同じ零行へ送る。 -/
def strictSimplicialStandardLeg (F : SimplicialObject (ModuleCategory A PUnit.{1}))
    (j : SimplexCategoryᵒᵖ) :
    (smallStrictBarCoefficientDiagram A F).obj j ⟶
      (strictSimplicialRealizationModule A F).obj (op PUnit.unit) :=
  (smallStrictBarCoefficientDiagram A F).map (sourceVertexSimplex (ComposableArrows.mk₀ j)).op ≫
    standardZeroLeg A (smallStrictBarCoefficientDiagram A F)

/-- 元の同じ増大まで合成すると、各対象の先頭頂点の標準脚に厳密に一致する。 -/
theorem strictSimplicialBarRealizationHom_vertex
    (F : SimplicialObject (ModuleCategory A PUnit.{1})) (j : SimplexCategoryᵒᵖ) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map
      (dgBarNativeVertexModuleMap A PUnit.{1} (smallStrictBarDiagram A F)
        (ULift.up (ComposableArrows.mk₀ j)) ≫ strictSimplicialBarRealizationHom A F) =
      strictSimplicialStandardLeg A F j := by
  rw [strictSimplicialBarRealizationHom, ← Category.assoc, Functor.map_comp,
    smallStrictBarNormalizedTotalHom_vertex, strictSimplicialBarAugmentation_point,
    replacementAugmentationTotalHomotopyEquiv_hom]
  rw [Category.assoc, standardZeroLeg_naturality]
  rw [← Category.assoc, ι_replacementAugmentation]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
