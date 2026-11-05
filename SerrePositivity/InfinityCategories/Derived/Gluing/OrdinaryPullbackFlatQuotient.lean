module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackObjects
public import SerrePositivity.InfinityCategories.Derived.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientFlatKernel
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientVerdierSequence
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
abbrev DGGluingPullbackFlatKernel :=
  resolvedDGQuotientFlatKernel R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
abbrev dgGluingPullbackFlatQuotientNerve :=
  resolvedDGQuotientNerve R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatQuotientFunctor :=
  resolvedDGQuotientFunctor R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatQuotientProjection :=
  resolvedDGQuotientProjection R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
def dgGluingPullbackFlatKernelInclusion :=
  resolvedDGQuotientFlatKernelInclusion R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
lemma dgGluingPullbackFlatKernel_small :
    Small.{u} (DGGluingPullbackFlatKernel R C D M) := inferInstance
lemma dgGluingPullbackFlatKernel_homKFlat :
    localHomKFlat R (DGGluingPullbackFlatKernel R C D M) :=
  resolvedDGQuotientFlatKernel_homKFlat R (DGGluingObject R C D M) _
def dgGluingPullbackFlatQuotientRoof :
    FunctorIso (dgNerve.map (DGCategoryCellResolution.augmentation R (DGGluingObject R C D M)) ≫
      dgGluingPullbackFlatQuotientFunctor R C D M)
      (dgGluingPullbackFlatQuotientProjection R C D M) :=
  resolvedDGQuotientFlatKernel_roof R (DGGluingObject R C D M) _
lemma dgGluingPullbackFlatQuotient_kills
    (x : (dgNerve R (DGGluingPullbackObject R C D M)) _⦋0⦌) :
    IsZeroVertex ((dgNerve.map (dgGluingPullbackInclusion R C D M) ≫
      dgGluingPullbackFlatQuotientFunctor R C D M).app (Opposite.op ⦋0⦌) x) :=
  resolvedDGQuotientNullFunctor_pointwise_zero R (DGGluingObject R C D M) _ x
variable (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackFlatKernel_isStable :
    IsStable (dgNerve R (DGGluingPullbackFlatKernel R C D M)) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact resolvedDGQuotientFlatKernel_isStable R (DGGluingObject R C D M) _
lemma dgGluingPullbackFlatQuotient_isStable :
    IsStable (dgGluingPullbackFlatQuotientNerve R C D M) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact resolvedDGQuotientNerve_isStable R (DGGluingObject R C D M) _
theorem dgGluingPullbackFlatKernel_isStableVerdierSequence :
    let := dgGluing_isDGPretriangulated R C D M hC hD
    let := dgCellResolutionSource_isDGPretriangulated R (DGGluingObject R C D M)
    let := dgNerve_isStable_of_pretriangulated R
      (DGCategoryCellResolution.Source R (DGGluingObject R C D M))
    let := dgGluingPullbackFlatKernel_isStable R C D M hC hD
    let := dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    IsStableVerdierSequence (dgNerve.map (dgGluingPullbackFlatKernelInclusion R C D M))
      (dgGluingPullbackFlatQuotientProjection R C D M) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  exact resolvedDGQuotientFlatKernel_isStableVerdierSequence R (DGGluingObject R C D M) _
end SerrePositivity.InfinityCategories
