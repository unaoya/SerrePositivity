module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseEdges
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFunctorSpace

/-!
概要：持ち上げた元の射の局所化性から、元の射の普遍性を回収する。
方針：持ち上げた標的だけで試験し、全前合成の充満忠実性と実延長を降ろす。
規約：局所化の値域の quasicategory 性を追加しない。
使われ方：局所化の二宇宙の比較の降下方向。順方向は別の主張。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization


/-- 持ち上げた任意の射を元の宇宙へ戻して再び持ち上げると、同じ全射になる。 -/
lemma uliftMorphismDown_up {X Y : SSet.{u}}
    (G : SSet.uliftFunctor.{v, u}.obj X ⟶ SSet.uliftFunctor.{v, u}.obj Y) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftMorphismDown G) = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  rfl

/-- 宇宙持ち上げ後に局所化である元の射は、元の宇宙でも局所化。 -/
lemma IsLocalization.of_ulift {X D : SSet.{u}} {F : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_fullyFaithful_extensions F W
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsEdges_ulift_iff F W).mp hF.choose)
  · intro E _
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful hF (SSet.uliftFunctor.{v, u}.obj E)
    have hD := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorSpaceIso.{u, v} D E)).isFullyFaithful
    have hX := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorSpaceIso.{u, v} X E)).isFullyFaithful
    have hc := hD.comp hp
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorSpaceIso.{u, v} D E).hom ≫
      (pre ((SSet.uliftFunctor.{v, u}).map F)).app (SSet.uliftFunctor.{v, u}.obj E)) at hc
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorSpaceIso_pre] at hc
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fullyFaithful_of_ulift (hX.cancel_right hc)
  · intro E _ L hL
    obtain ⟨G, ⟨e⟩⟩ := hF.exists_extension ((SSet.uliftFunctor.{v, u}).map L)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsEdges_ulift_iff L W).mpr hL)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftMorphismDown G, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functorIso_of_ulift ?_⟩⟩
    rw [Functor.map_comp, uliftMorphismDown_up G]
    exact e

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
