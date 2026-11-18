module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectivePinchedInclusion
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedEndpointMapNaturality

/-!
# 元の実 K-projective Hom 比較と全複体の同じ分解関手の作用

概要：実導来 Hom 比較は端点の等式輸送後に全複体側の同じ半自由分解の作用に一致する。
方針：元の包含に関する実正規化同型と端点輸送の自然性を合成する。
規約：元の分解関手・Hom 比較・二つの複体を保つ。
使われ方：元の自由単位を全複体上で導来 Hom の右脚へ接続する。
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

def kProjectiveAmbientDerivedEndpointIso (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val))
      ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
    (congrArg ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) X))
    (congrArg ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) Y))

lemma normalizedKProjectiveDerivedHomMap_ambient (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.ComplexLimits.normalizedKProjectiveDerivedHomMap A X Y ≫
      (_root_.SerrePositivity.ComplexLimits.kProjectiveAmbientDerivedEndpointIso A X Y).hom =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X.val Y.val).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val) := by
  have h := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val))
    (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso_inclusion A X Y)
  have hn := _root_.SerrePositivity.ComplexLimits.pinchedEndpointIso_map (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (D := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) Y)
  have hn' := congrArg (fun f => (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫ f) hn
  simp only [Category.assoc] at h
  have hh := hn'.symm.trans h
  exact hh

end SerrePositivity.ComplexLimits
