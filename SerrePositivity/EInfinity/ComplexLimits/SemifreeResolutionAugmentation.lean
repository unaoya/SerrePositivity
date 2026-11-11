module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeRingEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# 既存 D(R) 値解像から元の全複体への全 augmentation

概要：半自由出力分解の元の全比較を同じ一点評価で元の複体へ送る。
方針：二つの実 dg 評価の全 Hom の一致と元の実 augmentation を使う。
規約：同じ分解・同じ複体 dg nerve・全単体の比較を保持する。
使われ方：U の元の通常忘却への全比較の追跡。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma semifreeRingEvaluationDG_ambient :
    (semifreeRingEvaluationDG A).comp
      (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)) =
    (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty A PUnit.{1})).comp
        (moduleEvaluationDG A PUnit.{1} PUnit.unit) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro M N
  change ((moduleHomπ A PUnit.{1} M.val N.val PUnit.unit ≫ 𝟙 _) ≫ 𝟙 _) =
    𝟙 _ ≫ moduleHomπ A PUnit.{1} M.val N.val PUnit.unit
  simp only [Category.comp_id, Category.id_comp]

def complexSemifreeResolutionAugmentationHomotopy :
    SSet.Homotopy
      (complexSemifreeResolutionInfinity A ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) := by
  refine _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (HomotopyClasses.postHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy A (Complex A) PUnit.{1} (ringConstantDG A))) ?_ ?_
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty A PUnit.{1}))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (semifreeRingEvaluationDG A)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A))
    simp only [Category.assoc]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, semifreeRingEvaluationDG_ambient]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ringConstantDG A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ringConstantDG_comp_evaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]

end SerrePositivity.EInfinity.ComplexLimits
