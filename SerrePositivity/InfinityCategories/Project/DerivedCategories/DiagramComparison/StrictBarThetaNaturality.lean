module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarUnnormalizedComponents
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanModuleMap

/-!
概要：元のstrict図式の自然変換が、同じcoherent barのMC項とも可換することを示す。
方針：実barの鎖写像と元のgraded鎖写像の同じ成分を照合し、元の微分項を相殺する。
規約：MC項の可換性を仮定しない。全内部次数で元の等式を証明する。
使われ方：3b-3 R6、正規化barの関手と射影の全族の自然性への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の自然変換のgraded射は、元のMC項と各次数で可換する。 -/
@[reassoc]
lemma strictBarTheta_point_naturality
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) (q : ℤ) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarGradedMap A J η)).f q ≫
        (((moduleHomπ A PUnit.{1}
          (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)))
          (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G)))
          PUnit.unit).f 1 (dgCoherentBarTheta A PUnit.{1} (smallStrictBarDiagram A G))).v q (q + 1) rfl) =
      (((moduleHomπ A PUnit.{1}
          (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
          (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
          PUnit.unit).f 1 (dgCoherentBarTheta A PUnit.{1} (smallStrictBarDiagram A F))).v q (q + 1) rfl) ≫
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarGradedMap A J η)).f (q + 1) := by
  have hc := ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    (strictBarUnnormalizedMap A J η)).comm q (q + 1)
  change ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η)).f q ≫
      ((dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A G)).obj
        (op PUnit.unit)).d q (q + 1) =
    ((dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj
        (op PUnit.unit)).d q (q + 1) ≫
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η)).f (q + 1) at hc
  rw [dgCoherentBarModule_d, dgCoherentBarModule_d] at hc
  rw [strictBarUnnormalizedMap_component, strictBarUnnormalizedMap_component] at hc
  simp only [Preadditive.comp_add, Preadditive.add_comp] at hc
  have hg := ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    (strictBarGradedMap A J η)).comm q (q + 1)
  change ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarGradedMap A J η)).f q ≫
      ((ForgetEnrichment.to (Complex A)
        (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G))).obj (op PUnit.unit)).d q (q + 1) =
    ((ForgetEnrichment.to (Complex A)
        (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F))).obj (op PUnit.unit)).d q (q + 1) ≫
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarGradedMap A J η)).f (q + 1) at hg
  rw [hg] at hc
  exact add_left_cancel hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
