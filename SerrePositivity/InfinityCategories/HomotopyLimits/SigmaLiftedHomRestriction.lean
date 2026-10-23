module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLiftedHomRightKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeightTransport

/-!
概要：元の持ち上げた延長の全 Hom 族の制限を、元の図式の全 Hom 族へ比較する。
方針：元の指定単位からの回収同型を、同じ宇宙変更・反転・全共同 Hom へ写す。
規約：元の指定単位を使い、全 C と全標的係数の自然同型を保持する。
使われ方：全自然変換空間族の Yoneda 制限との全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の図式全体を持ち上げた、元の全標的係数の Hom 族。 -/
def liftedHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 2, u + 1}).map F₀)) ≫
    coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D)

/-- 元の指定単位から、持ち上げた延長の全 Hom 制限を元の図式の全族へ比較する。 -/
def sigmaLiftedHomFamily_restrictionIso
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))) ≫
      sigmaLiftedHomFamily G) (liftedHomWeightFamily F₀) := by
  have e := (FunctorIso.ulift.{u + 2, u + 3}
    (FunctorIso.ulift.{u + 1, u + 2} (sigmaLeftKanExtensionRecoveryIso β hβ)).op).postcomp
      (coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    sigmaLiftedHomFamily, liftedHomWeightFamily] using e

end SerrePositivity.InfinityCategories.HomotopyLimits
