module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects.OrdinaryPullbackObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Pretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientFlatKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientVerdierSequence
/-!
概要：元 gluing の通常 pullback 対象を零化する同じ cell 平坦商と実小核。
方針：D-9 の分解と商を同じ対象条件へ適用し、元の augmentation 屋根を保持する。
規約：核は分解上の実安定閉包。元から商への厳密 dg 射は要求しない。
使われ方：通常 pullback の完全包含と dg 側の Verdier 商の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
abbrev DGGluingPullbackFlatKernel :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
abbrev dgGluingPullbackFlatQuotientNerve :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatQuotientFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatQuotientProjection :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatKernelInclusion :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernelInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
lemma dgGluingPullbackFlatKernel_small :
    Small.{u} (DGGluingPullbackFlatKernel R C D M) := inferInstance
lemma dgGluingPullbackFlatKernel_homKFlat :
    _root_.SerrePositivity.DifferentialGraded.localHomKFlat R (DGGluingPullbackFlatKernel R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_homKFlat R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _
def dgGluingPullbackFlatQuotientRoof :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) ≫
      dgGluingPullbackFlatQuotientFunctor R C D M)
      (dgGluingPullbackFlatQuotientProjection R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_roof R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _
lemma dgGluingPullbackFlatQuotient_kills
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingPullbackObject R C D M)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackInclusion R C D M) ≫
      dgGluingPullbackFlatQuotientFunctor R C D M).app (Opposite.op ⦋0⦌) x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNullFunctor_pointwise_zero R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _ x
variable (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackFlatKernel_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGGluingPullbackFlatKernel R C D M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _
lemma dgGluingPullbackFlatQuotient_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgGluingPullbackFlatQuotientNerve R C D M) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _
theorem dgGluingPullbackFlatKernel_isStableVerdierSequence :
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R
      (DGCategoryCellResolution.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
    let := dgGluingPullbackFlatKernel_isStable R C D M hC hD
    let := dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgGluingPullbackFlatKernelInclusion R C D M))
      (dgGluingPullbackFlatQuotientProjection R C D M) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStableVerdierSequence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
