module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveDerivedComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementParameterEquivalence
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDerivedPinchedRoofFamily
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PinchedEndpointFamilyArrow
/-!
概要：元の K-projective 複体上の全要素屋根は実 D(R) の弱な pinched 族。
方針：既存の充満忠実な導来源と全要素パラメータの反転性を合成する。
規約：元の全屋根・同じ分解関手・元の複体頂点を保持する。
使われ方：標準単位の全族比較に使う弱な複体側基準射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.DifferentialGraded

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ分解関手の K-projective 頂点間の元の Hom 作用は弱同値。
方針：既存の包含と同じ導来源の充満忠実性から包含の Hom 作用を消去する。
規約：元の分解関手を保持。使われ方：元の全要素屋根の弱同値性。 -/
lemma complexSemifreeResolutionInfinity_pinchedMap_weak (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val)) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A)
  have hI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful A (Complex A)
    (_root_.SerrePositivity.ComplexLimits.complexKProjective A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :=
    hI.isQCatEquivalence.isWeakHomotopyEquivalence
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)
        (i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
        (i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
    have hk := _root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource_isFullyFaithful A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)
    exact hk.isQCatEquivalence.isWeakHomotopyEquivalence
  have h := hi.cancel_left hc
  have hx : i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) X
  have hy : i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) Y
  rw [hx, hy] at h
  exact h

/-- 概要：元の K-projective 全要素屋根の実導来 pinched 族自身は弱同値。
方針：元の全パラメータ射・実正規化 Hom 同型・同じ分解作用を合成する。
規約：元の実写像を保持。使われ方：複体側の弱な全族基準射。 -/
lemma normalizedTensorElementDerivedPinchedMap_weak (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap A X.val Y.val) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementParameterMap_localized_isIso A X.val Y.val)
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X.val Y.val)).isWeakHomotopyEquivalence
  exact (hp.comp hi).comp (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_pinchedMap_weak A X Y)

/-- 概要：同じ元の全要素屋根を通常導来源の実複体頂点の間へ送る。
方針：同じ ambient 頂点等式で端点だけを輸送する。
規約：元の全族を保持。使われ方：元の単位成分の定値三角形の比較射。 -/
def normalizedTensorElementOrdinaryPinchedMap (X Y : Complex A) :
    nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap A X Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A X).symm
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A Y).symm).hom

/-- 概要：同じ通常頂点の全 pinched 族は元の全複体屋根族を表す。
方針：元の全 Arrow 比較と端点輸送を合成し同じ始終域で反映する。
規約：全 h Fun の射の等式。使われ方：標準単位の全族三角形。 -/
lemma normalizedTensorElementOrdinaryPinchedMap_family (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) = _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A X Y := by
  apply Arrow.mk_injective _ _
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointFamily_arrow _ _
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap A X Y)).trans
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorDerivedPinchedFamily_arrow A X Y).trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily_arrow A X Y).symm)

/-- 概要：同じ通常頂点の K-projective 全要素族自身は弱同値。
方針：元の実導来全族と端点同型を合成する。
規約：元の写像を保持。使われ方：標準単位比較の弱な基準族。 -/
lemma normalizedTensorElementOrdinaryPinchedMap_weak (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap A X.val Y.val) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A X.val).symm
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A Y.val).symm
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap_weak A X Y).comp hi

end SerrePositivity.ComplexLimits
