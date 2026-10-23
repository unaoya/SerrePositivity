module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftClassification
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseTwistedArrowProjection
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction

/-!
概要：元の共同 Hom 全図式の宇宙変更を、持ち上げた元の圏の共同 Hom と比較する。
方針：全 twisted arrow 射影の厳密な宇宙正方形を分類し、両変数を同時に移す。
規約：全二変数の自然同型を保持し、対象対ごとの Hom 同値で代用しない。
使われ方：前層の指定宇宙変更と、元の全 Yoneda 関手との自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Compact
local instance {X : SSet.{u}} [Quasicategory X] : Quasicategory (X.op ⊗ X) :=
  quasicategory_of_innerFibration (CategoryTheory.CartesianMonoidalCategory.fst X.op X)
variable (C : SSet.{u}) [Quasicategory C]

/-- 元の全 twisted arrow 分類図式と、同じ指定宇宙変更の全自然比較。 -/
def twistedArrowHomUniverseIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (uliftTwistedArrowBaseIso.{u, u + 1} C).hom ≫
        twistedArrowHomInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (twistedArrowHomInfinity C) ≫
        spaceUniverseDiagram.{u}) :=
  leftClassification_squareIso ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C))
    (twistedArrowProjection ((SSet.uliftFunctor.{u + 1, u}).obj C))
    (uliftTwistedArrowIso C) (uliftTwistedArrowBaseIso C) (uliftTwistedArrowIso_projection C) ≪≫
      leftStraighteningInfinityDiagram_uliftIso (twistedArrowProjection C)

/-- 同じ大きい共同 Hom の両変数を、元の小さい両変数の全体へ戻す指定写像。 -/
def homInfinityUniverseBaseMap :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C).op ⊗
      (SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C) ⟶
    (SSet.uliftFunctor.{u + 2, u + 1}).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ C)) :=
  (uliftTensorIso _ _).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (uliftTwistedArrowBaseIso.{u, u + 1} C).inv

/-- 元の共同 Hom の指定宇宙変更は、持ち上げた元の圏の共同 Hom と全自然同型。 -/
def homInfinityJointUniverseIso :
    FunctorIso (homInfinityJointEvaluation ((SSet.uliftFunctor.{u + 1, u}).obj C))
      (homInfinityUniverseBaseMap C ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map (twistedArrowHomInfinity C) ≫
          spaceUniverseDiagram.{u}) := by
  have e := (twistedArrowHomUniverseIso C).precomp (homInfinityUniverseBaseMap C)
  have hl : homInfinityUniverseBaseMap C ≫
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (uliftTwistedArrowBaseIso.{u, u + 1} C).hom ≫
        twistedArrowHomInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) =
      homInfinityJointEvaluation ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
    dsimp only [homInfinityUniverseBaseMap, homInfinityJointEvaluation]
    rw [Category.assoc, ← Category.assoc
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (uliftTwistedArrowBaseIso.{u, u + 1} C).inv),
      ← Functor.map_comp, Iso.inv_hom_id]
    rw [(SSet.uliftFunctor.{u + 2, u + 1}).map_id, Category.id_comp]
  rw [hl] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
