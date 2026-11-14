module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.OverBousfieldKanCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.OverBousfieldKanColimitIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit

/-!
概要：通常の filtered 図式の Bousfield–Kan augmentation は弱ホモトピー同値。
方針：各 Over 圏の終対象での収縮を、実際の余極限表示同型を通して合成する。
規約：係数の値に Kan 性は不要。一般の coherent な図式は別工程。
使われ方：通常の filtered 余極限を空間の native な余極限に接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange


/-- 概要：通常の小さい filtered 図式の標準 augmentation は弱ホモトピー同値。
方針：Over 図式の余極限の成分ごとの弱同値と表示同型の二対三則を使う。
規約：任意の単体集合値の strict 図式。使われ方：通常の filtered 余極限模型の比較。 -/
lemma bousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitIso F)
  have he := hi.isWeakHomotopyEquivalence
  apply he.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanAugmentation F)
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison_augmentation]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanAugmentation_colimit_isWeakHomotopyEquivalence F

end SerrePositivity.InfinityCategories.Project.FilteredExchange
