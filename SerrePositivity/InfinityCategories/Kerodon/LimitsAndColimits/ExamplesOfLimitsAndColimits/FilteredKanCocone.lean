module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredKanColimitCanonical
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の filtered Kan 図式の任意の指定余極限余錐の native な余極限性。
方針：指定余極限同型で既証の反転 BK augmentation の弱同値を移す。
規約：元の余錐を保持し、F1b の filtered 余極限の主定理を再利用する。
使われ方：right fibration の同じ fiber 余錐を SpaceInfinity へ移す。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits


/-- 元の通常の filtered Kan 余錐の台が余極限なら、その同じ native 余錐も余極限。 -/
@[kerodon 03HS]
lemma strictNativeCocone_isColimit_of_filtered_forget
    {I : Type u} [SmallCategory I] [IsFiltered I] {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictNativeCocone_isColimit_of_reflectedAugmentation_weak
  let e := (colimit.isColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).coconePointUniqueUpToIso hc
  have he : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ≫ e.hom =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
    intro i
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation, e]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation, Category.assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation]
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
