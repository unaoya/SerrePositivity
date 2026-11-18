module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorPinchedDerivedRoof
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedFamilyPostcompArrow
/-! 概要：元の全 pinched 族を同じ導来 roof に同定する。
方針：全関手圏内の評価三角形と元の augmentation 逆を同じ関手で送る。
規約：全 K と端点輸送を保持。使われ方：標準単位比較自身の全高次比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorDerivedPinchedFamily_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
        ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
        ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y) := by
  exact (_root_.SerrePositivity.ComplexLimits.pinchedFamilyPostcomp_arrow (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y)).trans
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedFamilyPostDerived_arrow A X Y)

end SerrePositivity.ComplexLimits
