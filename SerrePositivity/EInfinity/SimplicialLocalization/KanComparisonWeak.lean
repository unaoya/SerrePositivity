module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanComparisonEnrichedFunctors
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalComparisonWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonalReductionWeak
public import SerrePositivity.EInfinity.Hammock.ExInfinityWeakMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
# 元の Kan 豊穣比較の各 Hom の同値性

概要：元の弱比較を同じ Ex∞ で送り、実 Kan Hom 間の圏同値を得る。
方針：構成済みの両弱比較・Ex∞ の弱同値保存・Kan Whitehead を使用する。
規約：元の比較の Hom 射そのものを保持する。
使われ方：元の coherent nerve の実比較の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : KanFreeHammockObjects C)

lemma kanFreeHammockAugmentationEnriched_map_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((kanFreeHammockAugmentationEnriched C).map X Y) :=
  Hammock.exInfinity_map_weak _ (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y)

lemma kanFreeHammockComparisonEnriched_map_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((kanFreeHammockComparisonEnriched C).map X Y) :=
  Hammock.exInfinity_map_weak _ (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)

lemma kanFreeHammockAugmentationEnriched_map_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((kanFreeHammockAugmentationEnriched C).map X Y) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (freeHammockDiagonalAugmentation C X Y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence _).mp
    (kanFreeHammockAugmentationEnriched_map_weak C X Y)

lemma kanFreeHammockComparisonEnriched_map_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((kanFreeHammockComparisonEnriched C).map X Y) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (freeHammockDiagonalComparison C X Y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence _).mp
    (kanFreeHammockComparisonEnriched_map_weak C X Y)

end SerrePositivity.EInfinity.SimplicialLocalization
