module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderNaturality

/-! # 全 Hom 自然な span の関手的な実円柱押し出し
概要：任意の元の span の左脚を同じ実写像円柱に替え、同じ右脚と押し出す。
方針：元の全 Hom 自然な源比較を span の標準 end に束ねる。
規約：全三頂点と両脚をパラメータにする。使われ方：実際の BF 帰納段。
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

/-- 同じ右脚と、同じ左脚の実円柱源比較からなる厳密豊穣 span。 -/
def pointedEnrichedCylinderPushoutSpan :
    EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u} :=
  pointedEnrichedSpanFunctor F (pointedEnrichedMappingCylinderFunctor F L l hl) R
    (pointedEnrichedMappingCylinderSource F L l hl) r
    (pointedEnrichedMappingCylinderSource_whisker F L l hl) hr

/-- 同じ実円柱と元の右脚の実押し出しを値とする厳密豊穣関手。 -/
def pointedEnrichedCylinderPushoutFunctor :
    EnrichedFunctor SSet.{u} C PointedSSetObject.{u} :=
  (pointedEnrichedCylinderPushoutSpan F L R l r hl hr).comp SSet pointedSpanPushoutEnrichedFunctor

/-- 元の同じ左標的から、同じ実押し出しへの比較。 -/
def pointedEnrichedCylinderPushoutLeft (X : C) :
    L.obj X ⟶ (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X :=
  pointedEnrichedMappingCylinderTarget F L l hl X ≫
    pointedSpanPushoutInl ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj X)

/-- 元の同じ右標的から、同じ実押し出しへの包含。 -/
def pointedEnrichedCylinderPushoutRight (X : C) :
    R.obj X ⟶ (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X :=
  pointedSpanPushoutInr ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj X)

/-- 実値は、同じ元の左脚の実写像円柱源射と右脚の押し出しそのもの。 -/
lemma pointedEnrichedCylinderPushoutFunctor_obj (X : C) :
    ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj =
      pushout (pointedTensorMappingCylinderSource (show (F.obj X).obj ⟶ (L.obj X).obj from l X))
        (show (F.obj X).obj ⟶ (R.obj X).obj from r X) := rfl

end SerrePositivity.KST.SConstruction
