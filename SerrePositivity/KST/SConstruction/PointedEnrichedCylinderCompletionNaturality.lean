module
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletion

/-! # 一般の実円柱 Kan 比較の全 Hom 自然性
概要：元の両標的比較と単位は、同じ Kan 値への全 Hom 自然な比較。
方針：同じ実押し出しの自然性へ、同じ Ex∞ 単位の自然性を合成する。
規約：全実成分と高次入力を保持。使われ方：BF の正の構造射と前向き比較。
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

/-- 同じ元の実押し出しから Kan 値への単位は全 Hom に自然。 -/
lemma pointedEnrichedCylinderCompletionUnit_whisker (X Y : C) :
    (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerLeft SSet ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X)
          (pointedEnrichedCylinderCompletionUnit F L R l r hl hr Y) =
      (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedCylinderCompletionUnit F L R l r hl hr X)
          ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj Y) :=
  enrichedExInfinityPointedUnit_whisker
    (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr) X Y

/-- 元の同じ左標的から Kan 値への比較は全 Hom に自然。 -/
lemma pointedEnrichedCylinderCompletionLeft_whisker (X Y : C) :
    L.map X Y ≫ eHomWhiskerLeft SSet (L.obj X)
        (pointedEnrichedCylinderCompletionLeft F L R l r hl hr Y) =
      (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedCylinderCompletionLeft F L R l r hl hr X)
          ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj Y) :=
  enriched_whisker_naturality_comp SSet (L.map X Y)
    ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y)
    ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).map X Y)
    (pointedEnrichedCylinderPushoutLeft F L R l r hl hr X)
    (pointedEnrichedCylinderPushoutLeft F L R l r hl hr Y)
    (pointedEnrichedCylinderCompletionUnit F L R l r hl hr X)
    (pointedEnrichedCylinderCompletionUnit F L R l r hl hr Y)
    (pointedEnrichedCylinderPushoutLeft_whisker F L R l r hl hr X Y)
    (pointedEnrichedCylinderCompletionUnit_whisker F L R l r hl hr X Y)

/-- 元の同じ右標的から Kan 値への比較は全 Hom に自然。 -/
lemma pointedEnrichedCylinderCompletionRight_whisker (X Y : C) :
    R.map X Y ≫ eHomWhiskerLeft SSet (R.obj X)
        (pointedEnrichedCylinderCompletionRight F L R l r hl hr Y) =
      (pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedCylinderCompletionRight F L R l r hl hr X)
          ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj Y) :=
  enriched_whisker_naturality_comp SSet (R.map X Y)
    ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y)
    ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).map X Y)
    (pointedEnrichedCylinderPushoutRight F L R l r hl hr X)
    (pointedEnrichedCylinderPushoutRight F L R l r hl hr Y)
    (pointedEnrichedCylinderCompletionUnit F L R l r hl hr X)
    (pointedEnrichedCylinderCompletionUnit F L R l r hl hr Y)
    (pointedEnrichedCylinderPushoutRight_whisker F L R l r hl hr X Y)
    (pointedEnrichedCylinderCompletionUnit_whisker F L R l r hl hr X Y)

end SerrePositivity.KST.SConstruction
