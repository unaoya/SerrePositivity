module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveDerivedSource
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionRetract
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso

/-!
# 同じ K-projective 導来源の全関手比較と充満忠実性

概要：実分解関手を半自由包含で戻すと、元の K-projective 包含と全関手同型になる。
方針：既存の射影的出力比較を同じ一点評価へ送り、充満忠実な包含で検出する。
規約：元の分解・全関手空間の同型を保つ。
使われ方：同じ cofibrant probe の実 Hom を既存 D(R) の Hom へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

def kProjectiveDerivedSourceInclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kProjectiveDerivedSource A ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (kProjectiveComplexInclusion A)) := by
  let I := kProjectiveComplexInclusion A
  let F := I.comp (ringConstantDG A)
  have hF (X : KProjectiveComplex A) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty A PUnit.{1} (F.obj X) :=
    (ringModule_homotopicallyProjective_iff A (ringModule A X.val)).mpr X.property
  have ep := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso A (KProjectiveComplex A) (Complex A)
      PUnit.{1} I (ringConstantDG A)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty A PUnit.{1})))
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (ep ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso A (KProjectiveComplex A) PUnit.{1} F hF)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit))
  have hEval : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty A PUnit.{1})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (semifreeRingEvaluationDG A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, semifreeRingEvaluationDG_ambient]
  have hTarget : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ringConstantDG A) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (moduleEvaluationDG A PUnit.{1} PUnit.unit) = 𝟙 _ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ringConstantDG_comp_evaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  dsimp only [F] at e
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] at e
  rw [hEval, hTarget, Category.comp_id] at e
  simpa only [kProjectiveDerivedSource, I, complexSemifreeResolutionInfinity,
    semifreeRingEvaluationInfinity, Category.assoc] using e

lemma kProjectiveDerivedSource_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kProjectiveDerivedSource A) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful A (Complex A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)).cancel_right
  exact (kProjectiveDerivedSourceInclusionIso A).isFullyFaithful_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful A (Complex A) (complexKProjective A))

end SerrePositivity.EInfinity.ComplexLimits
