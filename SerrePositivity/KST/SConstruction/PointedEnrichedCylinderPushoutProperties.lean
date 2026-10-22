module
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderPushout
public import SerrePositivity.KST.SConstruction.PointedDoubleMappingCylinderMono
public import SerrePositivity.KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence

/-! # 同じ一般の実円柱押し出しの単射性と弱比較
概要：元の両標的からの比較は単射、左脚が弱同値なら右比較は弱同値。
方針：元の実写像円柱と実押し出しの具体的な一般定理を適用する。
規約：右脚の単射性は不要。使われ方：BF の任意の正の帰納段。
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

/-- 元の同じ左標的からの比較は基礎単射。 -/
lemma pointedEnrichedCylinderPushoutLeft_mono (X : C) :
    Mono (show (L.obj X).obj ⟶
      ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj from
        pointedEnrichedCylinderPushoutLeft F L R l r hl hr X).right :=
  pointedDoubleMappingCylinderLeft_mono
    (show (F.obj X).obj ⟶ (L.obj X).obj from l X)
    (show (F.obj X).obj ⟶ (R.obj X).obj from r X)

/-- 元の同じ右標的からの比較は基礎単射。 -/
lemma pointedEnrichedCylinderPushoutRight_mono (X : C) :
    Mono (show (R.obj X).obj ⟶
      ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj from
        pointedEnrichedCylinderPushoutRight F L R l r hl hr X).right :=
  pointedDoubleMappingCylinderRight_mono
    (show (F.obj X).obj ⟶ (L.obj X).obj from l X)
    (show (F.obj X).obj ⟶ (R.obj X).obj from r X)

/-- 元の左脚が局所化可逆なら、同じ実押し出しの右比較も局所化可逆。 -/
lemma pointedEnrichedCylinderPushoutRight_localized_isIso (X : C)
    (hX : IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (show (F.obj X).obj ⟶ (L.obj X).obj from l X).right)) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (show (R.obj X).obj ⟶
        ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj from
          pointedEnrichedCylinderPushoutRight F L R l r hl hr X).right) := by
  let _ := hX
  exact pointedDoubleMappingCylinderRight_localized_isIso
    (show (F.obj X).obj ⟶ (L.obj X).obj from l X)
    (show (F.obj X).obj ⟶ (R.obj X).obj from r X)

/-- 元の二脚と同じ両標的比較は、局所化で可換。 -/
lemma pointedEnrichedCylinderPushout_localized_square (X : C) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (show (F.obj X).obj ⟶ (L.obj X).obj from l X).right ≫
        SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
          (show (L.obj X).obj ⟶
            ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj from
              pointedEnrichedCylinderPushoutLeft F L R l r hl hr X).right =
      SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
          (show (F.obj X).obj ⟶ (R.obj X).obj from r X).right ≫
        SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
          (show (R.obj X).obj ⟶
            ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj from
              pointedEnrichedCylinderPushoutRight F L R l r hl hr X).right :=
  pointedDoubleMappingCylinder_localized_square
    (show (F.obj X).obj ⟶ (L.obj X).obj from l X)
    (show (F.obj X).obj ⟶ (R.obj X).obj from r X)

end SerrePositivity.KST.SConstruction
