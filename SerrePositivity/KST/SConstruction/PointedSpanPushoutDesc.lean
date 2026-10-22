module
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutEnrichedFunctor

/-! # 同じ元の点つき押し出しからの余錐降下
概要：実 span の元の二成分を、同じ点つき押し出しからの射に降ろす。
方針：元の実 pushout の普遍性と両包含での回収を使う。
規約：全て同じ元の通常射。使われ方：写像円柱射影の全 Hom 自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 同じ元の点つき押し出しからの、指定した二成分の実降下。 -/
def pointedSpanPushoutDesc (X : PointedSpanDiagram.{u}) (Z : PointedSSetObject.{u})
    (l : X.diagram.obj .left ⟶ Z) (r : X.diagram.obj .right ⟶ Z)
    (h : X.diagram.map WalkingSpan.Hom.fst ≫ l = X.diagram.map WalkingSpan.Hom.snd ≫ r) :
    pointedSpanPushout X ⟶ Z :=
  show (pointedSpanPushout X).obj ⟶ Z.obj from
    pushout.desc (show (X.diagram.obj .left).obj ⟶ Z.obj from l)
      (show (X.diagram.obj .right).obj ⟶ Z.obj from r) h

/-- 同じ元の降下は、左包含で指定の左成分を回収する。 -/
lemma pointedSpanPushoutInl_desc (X : PointedSpanDiagram.{u}) (Z : PointedSSetObject.{u})
    (l : X.diagram.obj .left ⟶ Z) (r : X.diagram.obj .right ⟶ Z)
    (h : X.diagram.map WalkingSpan.Hom.fst ≫ l = X.diagram.map WalkingSpan.Hom.snd ≫ r) :
    pointedSpanPushoutInl X ≫ pointedSpanPushoutDesc X Z l r h = l :=
  pushout.inl_desc (f := pointedSpanPushoutLeftMap X) (g := pointedSpanPushoutRightMap X)
    (show (X.diagram.obj .left).obj ⟶ Z.obj from l)
    (show (X.diagram.obj .right).obj ⟶ Z.obj from r) h

/-- 同じ元の降下は、右包含で指定の右成分を回収する。 -/
lemma pointedSpanPushoutInr_desc (X : PointedSpanDiagram.{u}) (Z : PointedSSetObject.{u})
    (l : X.diagram.obj .left ⟶ Z) (r : X.diagram.obj .right ⟶ Z)
    (h : X.diagram.map WalkingSpan.Hom.fst ≫ l = X.diagram.map WalkingSpan.Hom.snd ≫ r) :
    pointedSpanPushoutInr X ≫ pointedSpanPushoutDesc X Z l r h = r :=
  pushout.inr_desc (f := pointedSpanPushoutLeftMap X) (g := pointedSpanPushoutRightMap X)
    (show (X.diagram.obj .left).obj ⟶ Z.obj from l)
    (show (X.diagram.obj .right).obj ⟶ Z.obj from r) h

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の豊穣 span 関手に前合成しても、左包含上の同じ全族を回収する。 -/
lemma pointedEnrichedSpanPushout_inl (F : EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u})
    (X Y : C) :
    (F.comp SSet pointedSpanPushoutEnrichedFunctor).map X Y ≫
        eHomWhiskerRight SSet (pointedSpanPushoutInl (F.obj X)) (pointedSpanPushout (F.obj Y)) =
      F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .left ≫
        eHomWhiskerLeft SSet ((F.obj X).diagram.obj .left) (pointedSpanPushoutInl (F.obj Y)) := by
  change (F.map X Y ≫ pointedSpanPushoutHom (F.obj X) (F.obj Y)) ≫ _ = _
  rw [Category.assoc, pointedSpanPushoutHom_inl (F.obj X) (F.obj Y)]
  rfl

/-- 元の豊穣 span 関手に前合成しても、右包含上の同じ全族を回収する。 -/
lemma pointedEnrichedSpanPushout_inr (F : EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u})
    (X Y : C) :
    (F.comp SSet pointedSpanPushoutEnrichedFunctor).map X Y ≫
        eHomWhiskerRight SSet (pointedSpanPushoutInr (F.obj X)) (pointedSpanPushout (F.obj Y)) =
      F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .right ≫
        eHomWhiskerLeft SSet ((F.obj X).diagram.obj .right) (pointedSpanPushoutInr (F.obj Y)) := by
  change (F.map X Y ≫ pointedSpanPushoutHom (F.obj X) (F.obj Y)) ≫ _ = _
  rw [Category.assoc, pointedSpanPushoutHom_inr (F.obj X) (F.obj Y)]
  rfl

end SerrePositivity.KST.SConstruction
