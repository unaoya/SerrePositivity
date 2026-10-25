module

public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseEdges
public import SerrePositivity.InfinityCategories.F1B.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFunctorIso
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFunctorSpace

/-!
概要：持ち上げた元の射の局所化性から、元の射の普遍性を回収する。
方針：持ち上げた標的だけで試験し、全前合成の充満忠実性と実延長を降ろす。
規約：局所化の値域の quasicategory 性を追加しない。
使われ方：局所化の二宇宙の比較の降下方向。順方向は別の主張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open LocalizationUniverse

/-- 持ち上げた任意の射を元の宇宙へ戻して再び持ち上げると、同じ全射になる。 -/
lemma uliftMorphismDown_up {X Y : SSet.{u}}
    (G : SSet.uliftFunctor.{v, u}.obj X ⟶ SSet.uliftFunctor.{v, u}.obj Y) :
    (SSet.uliftFunctor.{v, u}).map (uliftMorphismDown G) = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  rfl

/-- 宇宙持ち上げ後に局所化である元の射は、元の宇宙でも局所化。 -/
lemma IsLocalization.of_ulift {X D : SSet.{u}} {F : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hF : IsLocalization ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W)) :
    IsLocalization F W := by
  apply isLocalization_of_fullyFaithful_extensions F W
    ((invertsEdges_ulift_iff F W).mp hF.choose)
  · intro E _
    have hp := IsLocalization.precomposition_isFullyFaithful hF (SSet.uliftFunctor.{v, u}.obj E)
    have hD := (qCatEquivalenceOfIso (uliftFunctorSpaceIso.{u, v} D E)).isFullyFaithful
    have hX := (qCatEquivalenceOfIso (uliftFunctorSpaceIso.{u, v} X E)).isFullyFaithful
    have hc := hD.comp hp
    change IsFullyFaithful ((uliftFunctorSpaceIso.{u, v} D E).hom ≫
      (pre ((SSet.uliftFunctor.{v, u}).map F)).app (SSet.uliftFunctor.{v, u}.obj E)) at hc
    rw [← uliftFunctorSpaceIso_pre] at hc
    exact fullyFaithful_of_ulift (hX.cancel_right hc)
  · intro E _ L hL
    obtain ⟨G, ⟨e⟩⟩ := hF.exists_extension ((SSet.uliftFunctor.{v, u}).map L)
      ((invertsEdges_ulift_iff L W).mpr hL)
    refine ⟨uliftMorphismDown G, ⟨functorIso_of_ulift ?_⟩⟩
    rw [Functor.map_comp, uliftMorphismDown_up G]
    exact e

end SerrePositivity.InfinityCategories
