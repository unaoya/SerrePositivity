module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningCoherentEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningFullyFaithfulCriterion

/-!
概要：任意の底の実際の分類同値を、初頂点に沿う引き戻しの充満忠実性へ還元する。
方針：初頂点制限の関手同型の両側で、証明済みの充満忠実な後合成を消去する。
規約：初頂点写像自体を圏同値と仮定せず、局所化の前合成の充満忠実性だけを使う。
使われ方：通常の nerve 上で閉じた分類同値と、一般の底で残る条件の分離。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 一般の底の分類写像が充満忠実であることは、初頂点引き戻しの充満忠実性と同値。 -/
lemma leftStraighteningInfinityMap_isFullyFaithful_iff_firstVertexBaseChange
    (B : SSet.{u}) :
    IsFullyFaithful (leftStraighteningInfinityMap B) ↔
      IsFullyFaithful (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B)) := by
  have hp := localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B) SpaceInfinity.{u}
  have hc := leftStraighteningCoherentMap_isFullyFaithful (TransportSimplexCategory B)
  exact (isFullyFaithful_comp_iff _ _ hp).symm.trans
    ((leftStraighteningInfinityMap_firstVertexRestrictionIso B).isFullyFaithful_iff.trans
      (isFullyFaithful_comp_iff _ _ hc))

/-- 一般の底の元の分類写像が同値であるための残る条件は、初頂点引き戻しの充満忠実性。 -/
lemma leftStraighteningInfinityMap_isQCatEquivalence_iff_firstVertexBaseChange
    (B : SSet.{u}) :
    IsQCatEquivalence (leftStraighteningInfinityMap B) ↔
      IsFullyFaithful (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B)) := by
  constructor
  · intro h
    exact (leftStraighteningInfinityMap_isFullyFaithful_iff_firstVertexBaseChange B).mp
      h.isFullyFaithful
  · intro h
    exact isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
      ((leftStraighteningInfinityMap_isFullyFaithful_iff_firstVertexBaseChange B).mpr h)
      (leftStraighteningInfinityMap_isEssentiallySurjective B)

end SerrePositivity.InfinityCategories
