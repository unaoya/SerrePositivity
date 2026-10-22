module
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderPushout
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutDesc
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerNaturality

/-! # 同じ一般の実円柱押し出し比較の全 Hom 自然性
概要：元の両標的から同じ実円柱押し出しへの比較は、全入力族に自然。
方針：同じ標準 end の射影回収と、実円柱標的比較の全 Hom 自然性を合成する。
規約：三つの任意の実入力関手を保持。使われ方：BF の正の帰納段。
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

/-- 同じ実円柱から実押し出しへの包含は全 Hom に自然。 -/
lemma pointedEnrichedCylinderPushoutInl_whisker (X Y : C) :
    (pointedEnrichedMappingCylinderFunctor F L l hl).map X Y ≫
        eHomWhiskerLeft SSet ((pointedEnrichedMappingCylinderFunctor F L l hl).obj X)
          (pointedSpanPushoutInl ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj Y)) =
      (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet
          (pointedSpanPushoutInl ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj X))
          ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj Y) := by
  have h := pointedEnrichedSpanPushout_inl
    (pointedEnrichedCylinderPushoutSpan F L R l r hl hr) X Y
  have hp := pointedEnrichedSpanHom_projection F
    (pointedEnrichedMappingCylinderFunctor F L l hl) R
    (pointedEnrichedMappingCylinderSource F L l hl) r
    (pointedEnrichedMappingCylinderSource_whisker F L l hl) hr X Y .left
  rw [← Category.assoc] at h
  erw [hp] at h
  exact h.symm

/-- 同じ元の右標的からの比較は全 Hom に自然。 -/
lemma pointedEnrichedCylinderPushoutRight_whisker (X Y : C) :
    R.map X Y ≫ eHomWhiskerLeft SSet (R.obj X)
        (pointedEnrichedCylinderPushoutRight F L R l r hl hr Y) =
      (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedCylinderPushoutRight F L R l r hl hr X)
          ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj Y) := by
  have h := pointedEnrichedSpanPushout_inr
    (pointedEnrichedCylinderPushoutSpan F L R l r hl hr) X Y
  have hp := pointedEnrichedSpanHom_projection F
    (pointedEnrichedMappingCylinderFunctor F L l hl) R
    (pointedEnrichedMappingCylinderSource F L l hl) r
    (pointedEnrichedMappingCylinderSource_whisker F L l hl) hr X Y .right
  rw [← Category.assoc] at h
  erw [hp] at h
  exact h.symm

/-- 同じ元の左標的からの比較も全 Hom に自然。 -/
lemma pointedEnrichedCylinderPushoutLeft_whisker (X Y : C) :
    L.map X Y ≫ eHomWhiskerLeft SSet (L.obj X)
        (pointedEnrichedCylinderPushoutLeft F L R l r hl hr Y) =
      (pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedCylinderPushoutLeft F L R l r hl hr X)
          ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj Y) :=
  enriched_whisker_naturality_comp SSet (L.map X Y)
    ((pointedEnrichedMappingCylinderFunctor F L l hl).map X Y)
    ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).map X Y)
    (pointedEnrichedMappingCylinderTarget F L l hl X)
    (pointedEnrichedMappingCylinderTarget F L l hl Y)
    (pointedSpanPushoutInl ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj X))
    (pointedSpanPushoutInl ((pointedEnrichedCylinderPushoutSpan F L R l r hl hr).obj Y))
    (pointedEnrichedMappingCylinderTarget_whisker F L l hl X Y)
    (pointedEnrichedCylinderPushoutInl_whisker F L R l r hl hr X Y)

end SerrePositivity.KST.SConstruction
