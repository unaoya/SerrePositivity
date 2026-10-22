module
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderPushoutNaturality
public import SerrePositivity.KST.SConstruction.ExInfinityPointedUnitWhisker

/-! # 一般の実円柱押し出しの関手的 Kan 値化
概要：任意の元の span の円柱押し出しを同じ Ex∞ へ送る。
方針：全 Hom 自然な実押し出し関手を、元の Ex∞ 関手と合成する。
規約：元の両標的比較を保持。使われ方：BF の正の帰納段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F L R : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (l : ∀ X, F.obj X ⟶ L.obj X) (r : ∀ X, F.obj X ⟶ R.obj X)
  (hl : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (l Y) =
    L.map X Y ≫ eHomWhiskerRight SSet (l X) (L.obj Y))
  (hr : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (r Y) =
    R.map X Y ≫ eHomWhiskerRight SSet (r X) (R.obj Y))

/-- 同じ一般の実円柱押し出しの Ex∞ を値とする厳密豊穣関手。 -/
def pointedEnrichedCylinderCompletionFunctor :
    EnrichedFunctor SSet.{u} C PointedSSetObject.{u} :=
  (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).comp SSet
    exInfinityPointedEnrichedFunctor

/-- 同じ実 Kan 値と全 Hom を、Kan 対象の全部分圏に保持する。 -/
def pointedEnrichedCylinderCompletionKanFunctor :
    EnrichedFunctor SSet.{u} C PointedKanObject.{u} :=
  (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).comp SSet
    exInfinityPointedKanEnrichedFunctor

/-- 元の実押し出しから同じ Kan 値への単位成分。 -/
def pointedEnrichedCylinderCompletionUnit (X : C) :
    (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X ⟶
      (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X :=
  exInfinityPointedUnit ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X)

/-- 元の同じ左標的から Kan 値への前向き比較。 -/
def pointedEnrichedCylinderCompletionLeft (X : C) :
    L.obj X ⟶ (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X :=
  pointedEnrichedCylinderPushoutLeft F L R l r hl hr X ≫
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X

/-- 元の同じ右標的から Kan 値への前向き比較。 -/
def pointedEnrichedCylinderCompletionRight (X : C) :
    R.obj X ⟶ (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X :=
  pointedEnrichedCylinderPushoutRight F L R l r hl hr X ≫
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X

end SerrePositivity.KST.SConstruction
