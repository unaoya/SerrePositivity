module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
# 同じ複体解像の半自由部分圏での全 retract

概要：元の複体解像を既存 D(R) へ制限すると恒等関手と全関手同型になる。
方針：同じ出力解像の前合成比較と射影的出力の augmentation を評価する。
規約：既存半自由包含と同じ複体解像を保持する。
使われ方：離散入力の元の半自由解像との全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A]

def complexSemifreeResolutionRetractIso :
    FunctorIso (dgNerve.map (dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)) ≫
      complexSemifreeResolutionInfinity A) (𝟙 (derivedInfinityCategory A)) := by
  let I := dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)
  let F := I.comp (ringConstantDG A)
  have hF (X : Semifree A) : dgModuleProjectiveProperty A PUnit.{1} (F.obj X) :=
    moduleSemifree_homotopicallyProjective A PUnit.{1} X.property
  have ep := FunctorIso.postcomp
    (dgModuleResolvedInfinity_precompIso A (Semifree A) (Complex A)
      PUnit.{1} I (ringConstantDG A)).symm
    (dgNerve.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleSemifreeProperty A PUnit.{1})))
  have e := FunctorIso.postcomp
    (ep ≪≫ dgModuleResolvedInfinity_inclusionIso A (Semifree A) PUnit.{1} F hF)
    (dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit))
  have hEval : dgNerve.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleSemifreeProperty A PUnit.{1})) ≫
      dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
      dgNerve.map (semifreeRingEvaluationDG A) ≫ dgNerve.map I := by
    rw [← dgNerve.map_comp, ← dgNerve.map_comp, semifreeRingEvaluationDG_ambient]
  have hTarget : dgNerve.map (ringConstantDG A) ≫
      dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) = 𝟙 _ := by
    rw [← dgNerve.map_comp, ringConstantDG_comp_evaluation, dgNerve.map_id]
  dsimp only [F] at e
  simp only [dgNerve.map_comp, Category.assoc] at e
  rw [hEval, hTarget, Category.comp_id] at e
  apply (dgFullSubcategoryInclusionNerve_isFullyFaithful A (Complex A)
    (complexSemifree A)).preimageFunctorIso
  change FunctorIso ((dgNerve.map I ≫ complexSemifreeResolutionInfinity A) ≫
    dgNerve.map I) (𝟙 (dgNerve A (Semifree A)) ≫ dgNerve.map I)
  rw [Category.id_comp]
  simpa only [I, complexSemifreeResolutionInfinity, semifreeRingEvaluationInfinity,
    Category.assoc, Category.id_comp] using e

end SerrePositivity.EInfinity.ComplexLimits
