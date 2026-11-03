module

public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.BousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.OverBousfieldKanAugmentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.OverBousfieldKanCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.OverBousfieldKanColimitIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanColimit

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
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：通常の小さい filtered 図式の標準 augmentation は弱ホモトピー同値。
方針：Over 図式の余極限の成分ごとの弱同値と表示同型の二対三則を使う。
規約：任意の単体集合値の strict 図式。使われ方：通常の filtered 余極限模型の比較。 -/
lemma bousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ SSet.{u}) :
    IsWeakHomotopyEquivalence (bousfieldKanAugmentation F) := by
  have hi := isPrecompositionEquivalence_of_iso (overBousfieldKanColimitIso F)
  have he := hi.isWeakHomotopyEquivalence
  apply he.cancel_left
  change IsWeakHomotopyEquivalence
    (overBousfieldKanColimitComparison F ≫ bousfieldKanAugmentation F)
  rw [overBousfieldKanColimitComparison_augmentation]
  exact overBousfieldKanAugmentation_colimit_isWeakHomotopyEquivalence F

end SerrePositivity.InfinityCategories.F2
