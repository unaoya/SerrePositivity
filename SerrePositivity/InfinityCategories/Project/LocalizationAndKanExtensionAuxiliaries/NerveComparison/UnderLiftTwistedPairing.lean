module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CosliceTwistedArrowNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderTwistedPairing
/-! 同じ指定自然変換の全twisted pairingを元のcoslice表示から回収する。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 任意の同じ指定自然変換の全pairingをcoslice表示から厳密に回収する。 -/
lemma nerveUnderLift_comp_cosliceTwistedArrowMap {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    nerveMap (Under.lift V η) ≫ nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const I).obj (Opposite.op c)) V (fun i => η.app i)
        (fun {_ _} f => by simpa using (η.naturality f).symm) := by
  rw [nerveUnderMap_comp_cosliceTwistedArrowMap]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

/-- 指定モデル源で後合成した同じ全pairingの厳密な表示。 -/
lemma nerveUnderLift_comp_cosliceTwistedArrowMap_postcomp {I C : Type u}
    [Category.{u} I] [Category.{u} C] {c : C} {V : I ⥤ C}
    (η : (Functor.const I).obj c ⟶ V) {D : SSet.{u}} (F : nerve C ⟶ D) :
    nerveMap (Under.lift V η) ≫ nerveUnderMap c ≫ sliceUnderPostcomp (nervePoint c) F ≫
      cosliceTwistedArrowMap (nervePoint c ≫ F) =
      twistedPairingNerveMap ((Functor.const I).obj (Opposite.op c)) V (fun i => η.app i)
        (fun {_ _} f => by simpa using (η.naturality f).symm) ≫ edgewiseSubdivisionMap F := by
  rw [← SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceTwistedArrowMap_postcomp]
  simpa only [Category.assoc] using congrArg
    (fun f : nerve I ⟶ TwistedArrow (nerve C) => f ≫ edgewiseSubdivisionMap F)
    (nerveUnderLift_comp_cosliceTwistedArrowMap η)
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
end
