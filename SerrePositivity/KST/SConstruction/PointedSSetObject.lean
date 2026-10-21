module
public import SerrePositivity.KST.SConstruction.PointedClosedHomInclusion
public import SerrePositivity.KST.SConstruction.SSetInternalObject

/-! # 標準 basedHom を持つ点つき単体集合の対象
概要：同じ元の点つき単体集合と通常射を、標準の全 basedHom で豊穣化する。
方針：既存の標準点つき豊穣だけを専用型に移し、閉 Hom への包含を保持する。
規約：大域の既定 instance を変更しない。使われ方：同じ商の点つき豊穣関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

local instance pointedSSetObjectBase_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := Spectra.PointedEnrichment.simplicialCategory

/-- 同じ元の点つき単体集合を保持する、標準豊穣のための対象。 -/
structure PointedSSetObject where
  obj : PointedSimplicialSet.{u}

/-- 通常射は同じ元の基点を厳密に保存する射。 -/
instance pointedSSetObject_category : Category.{u} PointedSSetObject.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 元の標準 basedHom と同じ恒等・合成による豊穣。 -/
instance pointedSSetObject_enrichedCategory :
    EnrichedCategory SSet.{u} PointedSSetObject.{u} where
  Hom X Y := (PointedObject.basedHom X.obj Y.obj).right
  id X := eId SSet.{u} X.obj
  comp X Y Z := eComp SSet.{u} X.obj Y.obj Z.obj
  id_comp X Y := e_id_comp SSet.{u} X.obj Y.obj
  comp_id X Y := e_comp_id SSet.{u} X.obj Y.obj
  assoc W X Y Z := e_assoc SSet.{u} W.obj X.obj Y.obj Z.obj

/-- 元の通常の基点固定射は、同じ標準 basedHom の単位からの射に対応する。 -/
instance pointedSSetObject_simplicialCategory : SimplicialCategory PointedSSetObject.{u} where
  homEquiv {X Y} := eHomEquiv SSet.{u} (X := X.obj) (Y := Y.obj)
  homEquiv_id X := eHomEquiv_id SSet.{u} X.obj
  homEquiv_comp {X Y Z} f g := eHomEquiv_comp SSet.{u}
    (show X.obj ⟶ Y.obj from f) (show Y.obj ⟶ Z.obj from g)

/-- 豊穣だけを忘れ、同じ元の点つき対象と通常射を回収する。 -/
def pointedSSetObjectForget : PointedSSetObject.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := X.obj
  map f := f
  map_id _X := rfl
  map_comp _f _g := rfl

/-- 元の basedHom の包含を Hom 作用とする、基礎単体集合への厳密豊穣関手。 -/
def pointedSSetObjectClosedForget :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} SSetInternalObject.{u} where
  obj X := ⟨X.obj.right⟩
  map X Y := PointedObject.basedHomι X.obj Y.obj
  map_id X := pointedClosedHomInclusion_id X.obj
  map_comp X Y Z := pointedClosedHomInclusion_comp X.obj Y.obj Z.obj

/-- 同じ元の通常の基点固定射は、包含後も同じ基礎射として回収される。 -/
lemma pointedSSetObjectClosedForget_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet.{u} f ≫ pointedSSetObjectClosedForget.map X Y =
      curry' (show X.obj ⟶ Y.obj from f).right :=
  pointedClosedHomInclusion_hom (show X.obj ⟶ Y.obj from f)

end SerrePositivity.KST.SConstruction
