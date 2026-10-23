module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomWeightUniverseComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLiftedHomRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange

/-!
概要：元の Hom 係数の全評価族と、持ち上げた標的の全 Hom 制限族を自然同型で比較。
方針：元の全係数宇宙比較を、元の共同評価の二変数交換で写す。
規約：全 C・全標的の自然性を保持。Yoneda 自然変換空間の評価比較は別に残す。
使われ方：両右 Kan 族の制限比較における、係数評価側の全自然同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の係数前層の指定宇宙変更の全評価を、同じ両変数の全族として束ねる。 -/
def homWeightEvaluationFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  transposeFunctorFamily
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀) ≫
      presheafUniverseDiagram ((SSet.uliftFunctor.{u + 1, u}).obj C))

/-- 元の全係数評価族は、持ち上げた元の図式の全 Hom 制限族と自然同型。 -/
def homWeightEvaluationFamily_liftedIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    FunctorIso (homWeightEvaluationFamily F₀) (liftedHomWeightFamily F₀) := by
  have e := FunctorIso.transpose (presheafHomWeightDiagram_universeIso F₀)
  have hr : transposeFunctorFamily
      (presheafHomWeightDiagram ((SSet.uliftFunctor.{u + 2, u + 1}).map F₀)) =
      liftedHomWeightFamily F₀ :=
    presheafHomWeightDiagram_transpose _
  rw [hr] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
