module

public import SerrePositivity.EInfinity.SimplicialLocalization.ComparisonEnrichment

/-!
# 元の自由 hammock 対角の左右比較の実豊穣関手

概要：同じ両比較射を単位・合成を保つ豊穣関手へ束ねる。
方針：元の対角の空語の単位と全合成の正方形を使う。
規約：各 Hom の写像は既存の左右比較射そのもの。
使われ方：同じ Ex∞ を通す実 coherent nerve の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeHammockAugmentationEnriched :
    EnrichedFunctor SSet.{u} (FreeHammockObjects C) (HammockObjects C) where
  obj X := X
  map X Y := freeHammockDiagonalAugmentation C X Y
  map_id X := freeHammockDiagonalUnit_augmentation C X
  map_comp X Y Z := freeHammockDiagonalComposition_augmentation C X Y Z

def freeHammockComparisonEnriched :
    EnrichedFunctor SSet.{u} (FreeHammockObjects C) (LocalizationObjects C) where
  obj X := X
  map X Y := freeHammockDiagonalComparison C X Y
  map_id X := freeHammockDiagonalUnit_comparison C X
  map_comp X Y Z := freeHammockDiagonalComposition_comparison C X Y Z

lemma freeHammockAugmentationEnriched_map (X Y : FreeHammockObjects C) :
    (freeHammockAugmentationEnriched C).map X Y = freeHammockDiagonalAugmentation C X Y := rfl

lemma freeHammockComparisonEnriched_map (X Y : FreeHammockObjects C) :
    (freeHammockComparisonEnriched C).map X Y = freeHammockDiagonalComparison C X Y := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
