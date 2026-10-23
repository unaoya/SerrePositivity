module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLeftKanExtension
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：元の全図式の同型は、同じ図式の全 Hom 係数前層族の自然同型を与える。
方針：同じ同型を反転・宇宙持ち上げし、全前合成作用と元の Yoneda へ写す。
規約：P_Σ 延長では、元の指定単位の可逆性から構成済みの回収同型を使用する。
使われ方：左 Kan 延長の全 Hom 族と、元の C 上の係数前層族の制限比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全図式の指定同型から、全 Hom 係数前層族の同じ全自然同型を構成する。 -/
def presheafHomWeightDiagram_iso {C D : SSet.{u}} [Quasicategory D] {F G : C ⟶ D}
    (e : FunctorIso F G) :
    FunctorIso (presheafHomWeightDiagram F) (presheafHomWeightDiagram G) :=
  ((FunctorIso.ulift.{u, u + 1} e.op).map_pre SpaceInfinity.{u}).precomp (yonedaInfinityMap D)

/-- 元の延長の Hom 係数族の Yoneda 制限は、元の図式の全係数族と自然同型。 -/
def sigmaLeftKanHomWeightRestrictionIso {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D}
    {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    FunctorIso (presheafHomWeightDiagram G ≫
      presheafInfinityRestriction (sigmaYonedaInfinityMap C)) (presheafHomWeightDiagram F₀) := by
  rw [← presheafHomWeightDiagram_precomp]
  exact presheafHomWeightDiagram_iso (sigmaLeftKanExtensionRecoveryIso β hβ)

end SerrePositivity.InfinityCategories.HomotopyLimits
