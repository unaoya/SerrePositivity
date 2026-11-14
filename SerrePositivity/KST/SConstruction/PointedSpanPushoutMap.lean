module
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SimplicialHomWhisker

/-! # 元の自然変換による同じ実押し出し射の厳密な回収
概要：全 Hom の押し出し作用から、元の自然変換による同じ通常の押し出し射を回収する。
方針：両包含で比較し、元の end 評価と通常合成の豊穣表示を使う。
規約：同型を介さない射の等号。使われ方：写像円柱の元の通常射との一致。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 元の自然変換は、同じ実押し出しの貼り合わせ条件を保つ。 -/
lemma pointedSpanPushoutMap_condition {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) :
    X.diagram.map WalkingSpan.Hom.fst ≫ (t.app .left ≫ pointedSpanPushoutInl Y) =
      X.diagram.map WalkingSpan.Hom.snd ≫ (t.app .right ≫ pointedSpanPushoutInr Y) := by
  rw [← Category.assoc, t.naturality WalkingSpan.Hom.fst, Category.assoc,
    pointedSpanPushout_condition Y, ← Category.assoc, ← t.naturality WalkingSpan.Hom.snd,
    Category.assoc]

/-- 元の自然変換の両成分を、同じ実押し出しへ降ろした通常射。 -/
def pointedSpanPushoutMap {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) :
    pointedSpanPushout X ⟶ pointedSpanPushout Y :=
  show (pointedSpanPushout X).obj ⟶ (pointedSpanPushout Y).obj from
    pushout.desc
      (show (X.diagram.obj .left).obj ⟶ (pointedSpanPushout Y).obj from
        t.app .left ≫ pointedSpanPushoutInl Y)
      (show (X.diagram.obj .right).obj ⟶ (pointedSpanPushout Y).obj from
        t.app .right ≫ pointedSpanPushoutInr Y) (pointedSpanPushoutMap_condition t)

/-- 同じ通常の押し出し射は、左包含上で元の左成分を回収する。 -/
lemma pointedSpanPushoutInl_map {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) :
    pointedSpanPushoutInl X ≫ pointedSpanPushoutMap t = t.app .left ≫ pointedSpanPushoutInl Y :=
  pushout.inl_desc (f := pointedSpanPushoutLeftMap X)
    (g := pointedSpanPushoutRightMap X)
    (show (X.diagram.obj .left).obj ⟶ (pointedSpanPushout Y).obj from
      t.app .left ≫ pointedSpanPushoutInl Y)
    (show (X.diagram.obj .right).obj ⟶ (pointedSpanPushout Y).obj from
      t.app .right ≫ pointedSpanPushoutInr Y) (pointedSpanPushoutMap_condition t)

/-- 同じ通常の押し出し射は、右包含上で元の右成分を回収する。 -/
lemma pointedSpanPushoutInr_map {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) :
    pointedSpanPushoutInr X ≫ pointedSpanPushoutMap t = t.app .right ≫ pointedSpanPushoutInr Y :=
  pushout.inr_desc (f := pointedSpanPushoutLeftMap X)
    (g := pointedSpanPushoutRightMap X)
    (show (X.diagram.obj .left).obj ⟶ (pointedSpanPushout Y).obj from
      t.app .left ≫ pointedSpanPushoutInl Y)
    (show (X.diagram.obj .right).obj ⟶ (pointedSpanPushout Y).obj from
      t.app .right ≫ pointedSpanPushoutInr Y) (pointedSpanPushoutMap_condition t)

/-- 全 Hom の押し出し関手は、元の同じ通常の押し出し射を厳密に回収する。 -/
lemma pointedSpanPushoutEnrichedFunctor_hom {X Y : PointedSpanDiagram.{u}} (t : X ⟶ Y) :
    eHomEquiv SSet t ≫ pointedSpanPushoutEnrichedFunctor.map X Y =
      eHomEquiv SSet (pointedSpanPushoutMap t) := by
  change eHomEquiv SSet t ≫ pointedSpanPushoutHom X Y = _
  apply pointedSpanPushoutHom_ext X (pointedSpanPushout Y)
  · rw [Category.assoc, pointedSpanPushoutHom_inl X Y]
    change eHomEquiv SSet t ≫ (pointedSpanProjection X Y .left ≫ _) = _
    rw [← Category.assoc, pointedSpanProjection_hom t .left,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_post, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_pre, pointedSpanPushoutInl_map t]
  · rw [Category.assoc, pointedSpanPushoutHom_inr X Y]
    change eHomEquiv SSet t ≫ (pointedSpanProjection X Y .right ≫ _) = _
    rw [← Category.assoc, pointedSpanProjection_hom t .right,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_post, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialHom_pre, pointedSpanPushoutInr_map t]

end SerrePositivity.KST.SConstruction
