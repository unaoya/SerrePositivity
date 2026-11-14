module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeDerivedRetract
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedKProjectiveDerivedFamily
public import SerrePositivity.EInfinity.ComplexLimits.PinchedPostcompositionFamily

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedProbeDerivedHomMap_family (X Y : Complex A) (K : SSet.{u + 1})
    (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val)) :
    let Q := framedLimitKProjectiveProbe A X
    let T := semifreeKProjectiveTarget A Y
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ normalizedProbeDerivedHomMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
        ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ (normalizedKProjectiveHomIso A Q T).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (KProjectiveComplex A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (kProjectiveDerivedSource A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex T)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (normalizedProbeDerivedRetractHom A Y) := by
  dsimp only
  let Q := framedLimitKProjectiveProbe A X
  let T := semifreeKProjectiveTarget A Y
  have h := pinchedPostcompose_intervalFamily (normalizedProbeDerivedRetractHom A Y)
    (g ≫ normalizedKProjectiveDerivedHomMap A Q T)
  rw [normalizedProbeDerivedHomMap_eq_postcompose]
  simp only [Category.assoc] at h ⊢
  exact h.trans (congrArg (fun h => h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K
    (normalizedProbeDerivedRetractHom A Y))
    (normalizedKProjectiveDerivedHomMap_family A Q T K g))

end SerrePositivity.EInfinity.ComplexLimits
