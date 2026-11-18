module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeDerivedRetract
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedKProjectiveDerivedFamily
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedPostcompositionFamily

/-!
# 同じ半自由標的を持つ実導来 Hom 比較の全族公式

概要：右比較は同じ半自由分解関手の全族作用と同じ retract の後合成を表す。
方針：実 K-projective Hom の区間自然性と元の pinched 後合成の全族公式を合成する。
規約：同じ QX・S(Y)・分解関手・retract を任意 K で保つ。
使われ方：元の U 作用と自由単位への全三角形の右脚の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedProbeDerivedHomMap_family (X Y : Complex A) (K : SSet.{u + 1})
    (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val)) :
    let Q := _root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X
    let T := _root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A Y
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedHomMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
        ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A Q T).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.ComplexLimits.KProjectiveComplex A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedRetractHom A Y) := by
  dsimp only
  let Q := _root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X
  let T := _root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A Y
  have h := _root_.SerrePositivity.ComplexLimits.pinchedPostcompose_intervalFamily (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedRetractHom A Y)
    (g ≫ _root_.SerrePositivity.ComplexLimits.normalizedKProjectiveDerivedHomMap A Q T)
  rw [_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedHomMap_eq_postcompose]
  simp only [Category.assoc] at h ⊢
  exact h.trans (congrArg (fun h => h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedRetractHom A Y))
    (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveDerivedHomMap_family A Q T K g))

end SerrePositivity.ComplexLimits
