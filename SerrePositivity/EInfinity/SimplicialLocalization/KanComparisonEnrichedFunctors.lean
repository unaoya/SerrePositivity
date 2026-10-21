module

public import SerrePositivity.EInfinity.SimplicialLocalization.ComparisonEnrichedFunctors
public import SerrePositivity.EInfinity.SimplicialLocalization.KanEnrichment
public import SerrePositivity.EInfinity.Hammock.ExInfinityEnrichedFunctor

/-!
# 元の自由 hammock の左右比較の実 Kan 豊穣関手

概要：元の比較関手を同じ Ex∞ で Kan 化する。
方針：構成済みの monoidal 移送を両比較へ適用する。
規約：元の Hom 射への Ex∞ の像を全 Hom で回収する。
使われ方：元の coherent nerve の比較と ∞ 局所化関手の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.KST.Comparison
variable (C : RelativeCategory.{u})

abbrev KanHammockObjects := TransportEnrichment exInfinity.{u} (HammockObjects C)

abbrev KanFreeHammockObjects := TransportEnrichment exInfinity.{u} (FreeHammockObjects C)

def kanFreeHammockAugmentationEnriched :
    EnrichedFunctor SSet.{u} (KanFreeHammockObjects C) (KanHammockObjects C) :=
  Hammock.exInfinityEnrichedFunctor (freeHammockAugmentationEnriched C)

def kanFreeHammockComparisonEnriched :
    EnrichedFunctor SSet.{u} (KanFreeHammockObjects C) (KanLocalizationObjects C) :=
  Hammock.exInfinityEnrichedFunctor (freeHammockComparisonEnriched C)

lemma kanFreeHammockAugmentationEnriched_map (X Y : KanFreeHammockObjects C) :
    (kanFreeHammockAugmentationEnriched C).map X Y =
      exInfinity.map (freeHammockDiagonalAugmentation C X Y) := rfl

lemma kanFreeHammockComparisonEnriched_map (X Y : KanFreeHammockObjects C) :
    (kanFreeHammockComparisonEnriched C).map X Y =
      exInfinity.map (freeHammockDiagonalComparison C X Y) := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
