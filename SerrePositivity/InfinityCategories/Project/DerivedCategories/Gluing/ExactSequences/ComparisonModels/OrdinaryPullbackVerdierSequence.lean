module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.OrdinaryPullbackStableClosure
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_stableClosure_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M :=
  funext (fun X => propext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_stableClosure_iff R C D M hC hD X))
lemma dgGluingPullbackNerve_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingPullbackObject R C D M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _)) at h
  rw [dgGluingPullbackProperty_stableClosure_eq R C D M hC hD] at h
  exact h
theorem dgGluingPullback_isStableVerdierSequence :
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    let := dgGluingPullbackNerve_isStable R C D M hC hD
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackFlatQuotient_isStable R C D M hC hD
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackInclusion R C D M))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackFlatQuotientFunctor R C D M) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackFlatQuotient_isStable R C D M hC hD
  have transport (P : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
      (he : P = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
      (hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) P)))
      (hv : let := hs
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) P))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackFlatQuotientFunctor R C D M)) :
      let := dgGluingPullbackNerve_isStable R C D M hC hD
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackInclusion R C D M))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackFlatQuotientFunctor R C D M) := by
    subst P
    exact hv
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_isStableVerdierSequence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)
  exact transport _ (dgGluingPullbackProperty_stableClosure_eq R C D M hC hD)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _) h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
