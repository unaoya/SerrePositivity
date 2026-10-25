module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackStableClosure
/-!
概要：元の通常 pullback の dg 包含と同じ平坦商への関手は安定 Verdier 列をなす。
方針：実安定閉包との対象条件の一致を D-9 の元の Verdier 列へ代入する。
規約：左射は元の充満 dg 包含、右射は同じ cell 平坦屋根を使う。
使われ方：通常 pullback を零化する dg 側の商と ⊙ の同定に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_stableClosure_eq :
    dgStableClosureProperty R (DGGluingObject R C D M) (dgGluingPullbackProperty R C D M) =
      dgGluingPullbackProperty R C D M :=
  funext (fun X => propext (dgGluingPullbackProperty_stableClosure_iff R C D M hC hD X))
lemma dgGluingPullbackNerve_isStable :
    IsStable (dgNerve R (DGGluingPullbackObject R C D M)) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  have h := dgStableClosureNerve_isStable R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
  change IsStable (dgNerve R (DGFullSubcategory (DGGluingObject R C D M) _)) at h
  rw [dgGluingPullbackProperty_stableClosure_eq R C D M hC hD] at h
  exact h
theorem dgGluingPullback_isStableVerdierSequence :
    let := dgGluing_isDGPretriangulated R C D M hC hD
    let := dgNerve_isStable_of_pretriangulated R (DGGluingObject R C D M)
    let := dgGluingPullbackNerve_isStable R C D M hC hD
    let := dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    IsStableVerdierSequence (dgNerve.map (dgGluingPullbackInclusion R C D M))
      (dgGluingPullbackFlatQuotientFunctor R C D M) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  let := dgNerve_isStable_of_pretriangulated R (DGGluingObject R C D M)
  let := dgGluingPullbackFlatQuotient_isStable R C D M hC hD
  have transport (P : Set (DGGluingObject R C D M))
      (he : P = dgGluingPullbackProperty R C D M)
      (hs : IsStable (dgNerve R (DGFullSubcategory (DGGluingObject R C D M) P)))
      (hv : let := hs
        IsStableVerdierSequence
          (dgNerve.map (dgFullSubcategoryInclusion R (DGGluingObject R C D M) P))
          (dgGluingPullbackFlatQuotientFunctor R C D M)) :
      let := dgGluingPullbackNerve_isStable R C D M hC hD
      IsStableVerdierSequence (dgNerve.map (dgGluingPullbackInclusion R C D M))
        (dgGluingPullbackFlatQuotientFunctor R C D M) := by
    subst P
    exact hv
  have h := resolvedDGQuotient_isStableVerdierSequence R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
  exact transport _ (dgGluingPullbackProperty_stableClosure_eq R C D M hC hD)
    (dgStableClosureNerve_isStable R (DGGluingObject R C D M) _) h
end SerrePositivity.InfinityCategories
