module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectivePinchedInclusion
public import SerrePositivity.EInfinity.ComplexLimits.PinchedEndpointMapNaturality

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

def kProjectiveAmbientDerivedEndpointIso (X Y : KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val))
      ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
    (congrArg ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) X))
    (congrArg ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) Y))

lemma normalizedKProjectiveDerivedHomMap_ambient (X Y : KProjectiveComplex A) :
    normalizedKProjectiveDerivedHomMap A X Y ≫
      (kProjectiveAmbientDerivedEndpointIso A X Y).hom =
    (normalizedTensorPinchedIso A X.val Y.val).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (complexSemifreeResolutionInfinity A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val) := by
  have h := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val))
    (normalizedKProjectiveHomIso_inclusion A X Y)
  have hn := pinchedEndpointIso_map (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) (complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (kProjectiveComplexInclusion A) Y)
  have hn' := congrArg (fun f => (normalizedKProjectiveHomIso A X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (kProjectiveComplexInclusion A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫ f) hn
  simp only [Category.assoc] at h
  have hh := hn'.symm.trans h
  exact hh

end SerrePositivity.EInfinity.ComplexLimits
