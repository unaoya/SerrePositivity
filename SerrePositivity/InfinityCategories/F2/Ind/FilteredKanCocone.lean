module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FilteredKanColimitCanonical

/-!
概要：通常の filtered Kan 図式の任意の指定余極限余錐の native な余極限性。
方針：指定余極限同型で既証の反転 BK augmentation の弱同値を移す。
規約：元の余錐を保持し、F1b の filtered 余極限の主定理を再利用する。
使われ方：right fibration の同じ fiber 余錐を SpaceInfinity へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 元の通常の filtered Kan 余錐の台が余極限なら、その同じ native 余錐も余極限。 -/
lemma strictNativeCocone_isColimit_of_filtered_forget
    {I : Type u} [SmallCategory I] [IsFiltered I] {F : I ⥤ KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c)) :
    IsColimitCone (strictNativeCocone c) := by
  apply strictNativeCocone_isColimit_of_reflectedAugmentation_weak
  let e := (colimit.isColimit (F ⋙ kanObjectForget)).coconePointUniqueUpToIso hc
  have he : reflectedBousfieldKanAugmentation (F ⋙ kanObjectForget) ≫ e.hom =
      weightedColimitAugmentation (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor)
        (kanObjectForget.mapCocone c) := by
    apply weightedColimit_hom_ext
    intro i
    dsimp only [reflectedBousfieldKanAugmentation, e]
    rw [← Category.assoc, weightedColimitι_augmentation, Category.assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom, weightedColimitι_augmentation]
  rw [← he]
  exact (reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered _).comp
    (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
