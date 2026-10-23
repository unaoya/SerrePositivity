module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaHomWeightRightKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeightTransport

/-!
概要：元の全自然変換空間族の Yoneda 制限を、元の大きい Yoneda の全族へ比較する。
方針：元の全 Yoneda 宇宙比較を反転・持ち上げし、同じ全共同 Hom と係数制限へ写す。
規約：全 C と全標的係数の自然同型を保持する。
使われ方：両右 Kan 族の元の制限の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の大きい Yoneda から、元の全 Hom 係数前層への自然変換空間を束ねた全族。 -/
def yonedaHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map
      (SSet.opFunctor.map (yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C))) ≫
    coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}

/-- 元の自然変換空間族の制限は、大きい元の Yoneda の全族と自然同型。 -/
def sigmaHomWeightFamily_restrictionIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))) ≫
      sigmaHomWeightFamily F₀) (yonedaHomWeightFamily F₀) := by
  have e := (FunctorIso.ulift.{u + 2, u + 3} (sigmaUniverseYonedaIso C).op).postcomp
    (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2})
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    sigmaHomWeightFamily, yonedaHomWeightFamily] using e

end SerrePositivity.InfinityCategories.HomotopyLimits
