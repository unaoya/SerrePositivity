module

public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseMorphismUp
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFunctorSpace
public import SerrePositivity.InfinityCategories.F1B.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：小さい射の充満忠実性と、小さい標的に対する全前合成の宇宙持ち上げ。
方針：同じ pinched Hom と関手空間の厳密同型で共役する。
規約：任意の大きい標的への充満忠実性はこの補題だけでは主張しない。
使われ方：Ind-S (4) の大きい境界資料を小模型へ落とした後の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.LocalizationUniverse

/-- 同じ射の充満忠実性は宇宙の持ち上げで保たれる。 -/
lemma fullyFaithful_ulift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (h : IsFullyFaithful f) :
    IsFullyFaithful ((SSet.uliftFunctor.{v, u}).map f) := by
  rintro ⟨x⟩ ⟨y⟩
  have hc := (IsSimplicialHomotopyEquivalence.ulift.{u, v} (h x y)).comp
    (homotopyEquivalence_of_iso (uliftPinchedHomIso.{u, v}
      (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)))
  rw [uliftPinchedHomIso_naturality] at hc
  exact (homotopyEquivalence_of_iso (uliftPinchedHomIso.{u, v} x y)).cancel_left hc

/-- 小さい標的を持ち上げた関手圏では、元の局所化の全前合成は充満忠実。 -/
lemma precomposition_fullyFaithful_ulift_target {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (hF : IsLocalization F W) (Q : SSet.{u}) [Quasicategory Q] :
    IsFullyFaithful ((pre ((SSet.uliftFunctor.{v, u}).map F)).app
      ((SSet.uliftFunctor.{v, u}).obj Q)) := by
  have hc := (fullyFaithful_ulift.{u, v} (hF.precomposition_isFullyFaithful Q)).comp
    (qCatEquivalenceOfIso (uliftFunctorSpaceIso.{u, v} X Q)).isFullyFaithful
  change IsFullyFaithful ((SSet.uliftFunctor.{v, u}).map ((pre F).app Q) ≫
    (uliftFunctorSpaceIso.{u, v} X Q).hom) at hc
  rw [uliftFunctorSpaceIso_pre] at hc
  have hh := (qCatEquivalenceOfIso (uliftFunctorSpaceIso.{u, v} D Q).symm).isFullyFaithful.comp hc
  change IsFullyFaithful ((uliftFunctorSpaceIso.{u, v} D Q).inv ≫
    ((uliftFunctorSpaceIso.{u, v} D Q).hom ≫
      (pre ((SSet.uliftFunctor.{v, u}).map F)).app ((SSet.uliftFunctor.{v, u}).obj Q))) at hh
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hh

end SerrePositivity.InfinityCategories.LocalizationUniverse
