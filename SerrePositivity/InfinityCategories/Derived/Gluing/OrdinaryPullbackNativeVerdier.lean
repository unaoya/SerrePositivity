module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackKernelLocalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackVerdierSequence
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
/-!
概要：元の通常 pullback 包含と同じ平坦商は Sp の実 Verdier 列をなす。
方針：既存の完全性に D-16 の厚い核反映・辺局所化を接続する。
規約：native nerve と同じ元二射を使い、追加宇宙の局所化を仮定で埋めない。
使われ方：dg 側の通常 pullback 商と Sp の IsVerdierSequence の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
def dgGluingNativeStableObject : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max u v w} where
  obj := dgNerve R (DGGluingObject R C D M)
  isQuasicategory := inferInstance
  isStable := by
    let := dgGluing_isDGPretriangulated R C D M hC hD
    exact dgNerve_isStable_of_pretriangulated R _
def dgGluingPullbackNativeStableObject : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max u v w} where
  obj := dgNerve R (DGGluingPullbackObject R C D M)
  isQuasicategory := inferInstance
  isStable := dgGluingPullbackNerve_isStable R C D M hC hD
def dgGluingPullbackNativeStableQuotient : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max u v w} where
  obj := dgGluingPullbackFlatQuotientNerve R C D M
  isQuasicategory := inferInstance
  isStable := dgGluingPullbackFlatQuotient_isStable R C D M hC hD
def dgGluingPullbackNativeStableInclusion :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingPullbackNativeStableObject R C D M hC hD)
      (dgGluingNativeStableObject R C D M hC hD) where
  hom := dgNerve.map (dgGluingPullbackInclusion R C D M)
  isExact := by
    let := dgGluing_isDGPretriangulated R C D M hC hD
    let : IsStable (dgNerve R (DGGluingPullbackObject R C D M)) :=
      dgGluingPullbackNerve_isStable R C D M hC hD
    let : IsStable (dgNerve R (DGGluingObject R C D M)) :=
      dgNerve_isStable_of_pretriangulated R _
    let : IsStable (dgGluingPullbackFlatQuotientNerve R C D M) :=
      dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    exact (dgGluingPullback_isStableVerdierSequence R C D M hC hD).inclusionExact
def dgGluingPullbackNativeStableProjection :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingNativeStableObject R C D M hC hD)
      (dgGluingPullbackNativeStableQuotient R C D M hC hD) where
  hom := dgGluingPullbackFlatQuotientFunctor R C D M
  isExact := by
    let := dgGluing_isDGPretriangulated R C D M hC hD
    let : IsStable (dgNerve R (DGGluingPullbackObject R C D M)) :=
      dgGluingPullbackNerve_isStable R C D M hC hD
    let : IsStable (dgNerve R (DGGluingObject R C D M)) :=
      dgNerve_isStable_of_pretriangulated R _
    let : IsStable (dgGluingPullbackFlatQuotientNerve R C D M) :=
      dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    exact (dgGluingPullback_isStableVerdierSequence R C D M hC hD).quotientExact
theorem dgGluingPullback_isNativeVerdierSequence :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence (dgGluingPullbackNativeStableInclusion R C D M hC hD)
      (dgGluingPullbackNativeStableProjection R C D M hC hD) where
  fullyFaithful := by
    let := dgGluing_isDGPretriangulated R C D M hC hD
    let : IsStable (dgNerve R (DGGluingPullbackObject R C D M)) :=
      dgGluingPullbackNerve_isStable R C D M hC hD
    let : IsStable (dgNerve R (DGGluingObject R C D M)) :=
      dgNerve_isStable_of_pretriangulated R _
    let : IsStable (dgGluingPullbackFlatQuotientNerve R C D M) :=
      dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    exact (dgGluingPullback_isStableVerdierSequence R C D M hC hD).fullyFaithful
  kernel := dgGluingPullbackFlatQuotient_zero_iff R C D M hC hD
  quotient := dgGluingPullbackFlatQuotient_isLocalization R C D M hC hD
end SerrePositivity.InfinityCategories
