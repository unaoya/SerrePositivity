module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeRingEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
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
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma semifreeRingEvaluationDG_ambient :
    (semifreeRingEvaluationDG A).comp
      (dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)) =
    (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleSemifreeProperty A PUnit.{1})).comp
        (moduleEvaluationDG A PUnit.{1} PUnit.unit) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro M N
  change ((moduleHomπ A PUnit.{1} M.val N.val PUnit.unit ≫ 𝟙 _) ≫ 𝟙 _) =
    𝟙 _ ≫ moduleHomπ A PUnit.{1} M.val N.val PUnit.unit
  simp only [Category.comp_id, Category.id_comp]

def complexSemifreeResolutionAugmentationHomotopy :
    SSet.Homotopy
      (complexSemifreeResolutionInfinity A ≫
        dgNerve.map (dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)))
      (𝟙 (dgNerve A (Complex A))) := by
  refine stableHomotopyRetarget
    (HomotopyClasses.postHomotopy (dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit))
      (dgModuleResolvedAugmentationHomotopy A (Complex A) PUnit.{1} (ringConstantDG A))) ?_ ?_
  · change (dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
        dgNerve.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1}))) ≫
        dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
      (dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
        dgNerve.map (semifreeRingEvaluationDG A)) ≫
        dgNerve.map (dgFullSubcategoryInclusion A (Complex A) (complexSemifree A))
    simp only [Category.assoc]
    rw [← dgNerve.map_comp, ← dgNerve.map_comp, semifreeRingEvaluationDG_ambient]
  · change dgNerve.map (ringConstantDG A) ≫
      dgNerve.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) = _
    rw [← dgNerve.map_comp, ringConstantDG_comp_evaluation, dgNerve.map_id]

end SerrePositivity.EInfinity.ComplexLimits
