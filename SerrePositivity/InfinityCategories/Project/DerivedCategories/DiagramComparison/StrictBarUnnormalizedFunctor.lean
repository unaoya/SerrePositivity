module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedNaturalComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalIso
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：元の非正規化coherent barを、指定された全複体同型に沿ってstrict図式の関手にする。
方針：既存の同じ比較同型で、元の単体的置換の全複体への射を共役し、一点評価で戻す。
規約：全複体同型はsmallStrictBarTotalPointIsoに固定する。native余錐の自然性は別に証明する。
使われ方：3b-3 R6、正規化barの自然性と同じ増大の全関手比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の係数図式の単体的置換の、直和全複体の通常関手。 -/
def strictBarTotalComplexFunctor : (J ⥤ ModuleCategory A PUnit.{1}) ⥤ Complex A :=
  (Functor.whiskeringRight J (ModuleCategory A PUnit.{1}) (Complex A)).obj (moduleEvaluation A PUnit.{1} PUnit.unit) ⋙
    simplicialReplacementFunctor (J := J) (C := Complex A) ⋙ directSumTotalFunctor A

/-- 指定全複体同型の共役で得る、元の非正規化bar上の射。 -/
def strictBarUnnormalizedMap {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    ForgetEnrichment.of (Complex A)
        (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ⟶
      ForgetEnrichment.of (Complex A)
        (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A G)) :=
  (moduleEvaluation A PUnit.{1} PUnit.unit).preimage
    ((smallStrictBarTotalPointIso A F).hom ≫
      (strictBarTotalComplexFunctor A J).map η ≫ (smallStrictBarTotalPointIso A G).inv)

/-- 一点評価は、元の指定比較同型による同じ共役を厳密に回収する。 -/
lemma strictBarUnnormalizedMap_evaluation {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η) =
      (smallStrictBarTotalPointIso A F).hom ≫
        (strictBarTotalComplexFunctor A J).map η ≫ (smallStrictBarTotalPointIso A G).inv :=
  Functor.map_preimage _ _

/-- 元の非正規化coherent barを、同じ比較同型に固定した全通常関手。 -/
def strictBarUnnormalizedFunctor : (J ⥤ ModuleCategory A PUnit.{1}) ⥤ ModuleCategory A PUnit.{1} where
  obj F := ForgetEnrichment.of (Complex A)
    (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
  map η := strictBarUnnormalizedMap A J η
  map_id F := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    rw [strictBarUnnormalizedMap_evaluation,
      (moduleEvaluation A PUnit.{1} PUnit.unit).map_id,
      (strictBarTotalComplexFunctor A J).map_id]
    change (smallStrictBarTotalPointIso A F).hom ≫
      (𝟙 _ ≫ (smallStrictBarTotalPointIso A F).inv) = 𝟙 _
    rw [Category.id_comp, Iso.hom_inv_id]
  map_comp η θ := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    rw [Functor.map_comp, strictBarUnnormalizedMap_evaluation,
      strictBarUnnormalizedMap_evaluation, strictBarUnnormalizedMap_evaluation,
      (strictBarTotalComplexFunctor A J).map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 同じ全複体比較は、共役で構成したbar関手の全図式・全射に自然。 -/
def strictBarUnnormalizedTotalIso :
    strictBarUnnormalizedFunctor A J ⋙ moduleEvaluation A PUnit.{1} PUnit.unit ≅
      strictBarTotalComplexFunctor A J :=
  NatIso.ofComponents (fun F => smallStrictBarTotalPointIso A F) (by
    intro F G η
    change (moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η) ≫
      (smallStrictBarTotalPointIso A G).hom =
        (smallStrictBarTotalPointIso A F).hom ≫ (strictBarTotalComplexFunctor A J).map η
    rw [strictBarUnnormalizedMap_evaluation]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
