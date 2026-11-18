module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.ElementsCoconeAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.KanCoconeAugmentationCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.NerveLeftQuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence

/-!
概要：集合値の同じ余錐の元の増大の弱同値性を、実際の離散空間値余錐の余極限性へ渡す。
方針：構成済みの反転 BK 比較の同じ増大の式を、既存の Kan 余錐の判定に入れる。
規約：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の既存の判定の接続の法則。
使われ方：S8 の各点の Čech 余錐。元の余錐をそのまま使い、余極限の存在を入力にしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I] {P : I ⥤ Type u}

/-- 元の要素圏の増大の弱同値性で、同じ離散空間値の余錐の余極限性を判定する。 -/
lemma strictSetCocone_isColimit_of_elementsAugmentation_weak (c : Cocone P)
    (hc : IsWeakHomotopyEquivalence (elementsCoconeAugmentation c)) :
    IsColimitCone (strictNativeCocone (setsToKan.mapCocone c)) := by
  apply strictNativeCocone_isColimit_of_reflectedAugmentation_weak
  change IsWeakHomotopyEquivalence (weightedColimitAugmentation _ (setCoconeCoefficients c))
  rw [← reflectedBousfieldKanElementsIso_augmentation]
  exact (isPrecompositionEquivalence_of_iso (reflectedBousfieldKanElementsIso P)).isWeakHomotopyEquivalence.comp hc

/-- 元の要素圏の増大の各 comma の収縮を、同じ空間値余錐の普遍性へ渡す。 -/
lemma strictSetCocone_isColimit_of_contractible_comma (c : Cocone P)
    (hc : ∀ q : Discrete c.pt,
      IsWeaklyContractible (nerve (CostructuredArrow (elementsCoconeFunctor c) q))) :
    IsColimitCone (strictNativeCocone (setsToKan.mapCocone c)) := by
  apply strictSetCocone_isColimit_of_elementsAugmentation_weak
  exact (nerveMap_isLeftCofinal_of_weaklyContractible_comma (elementsCoconeFunctor c) hc).isWeakHomotopyEquivalence.comp
      ((isPrecompositionEquivalence_of_iso
        (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso
          c.pt)).isWeakHomotopyEquivalence)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
