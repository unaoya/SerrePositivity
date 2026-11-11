module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPinchedDerivedRoof
public import SerrePositivity.EInfinity.ComplexLimits.PinchedFamilyPostcompArrow
/-! 概要：元の全 pinched 族を同じ導来 roof に同定する。
方針：全関手圏内の評価三角形と元の augmentation 逆を同じ関手で送る。
規約：全 K と端点輸送を保持。使われ方：標準単位比較自身の全高次比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorDerivedPinchedFamily_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (normalizedTensorElementDerivedPinchedMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
        ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
        ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))) =
      Arrow.mk (normalizedTensorElementDerivedRoof A X Y) := by
  exact (pinchedFamilyPostcomp_arrow (complexSemifreeResolutionInfinity A)
    (normalizedTensorElementPinchedMap A X Y)).trans
      (normalizedTensorPinchedFamilyPostDerived_arrow A X Y)

end SerrePositivity.EInfinity.ComplexLimits
