module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial

/-! # 閉内部 Hom を保持する単体集合の圏
概要：任意の実単体集合を、同じ閉内部 Hom による単体的圏の対象にする。
方針：閉構造の単位・合成と curry による通常射の表示を使う。
規約：SSet の既定の外側の豊穣は変えない。使われ方：対角実現と豊穣 Kan 置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 閉内部 Hom の豊穣を選ぶために保持した、同じ実単体集合。 -/
structure SSetInternalObject where
  obj : SSet.{u}

/-- 通常射は、元の同じ単体集合の射。 -/
instance sSetInternalObject_category : Category.{u} SSetInternalObject.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 全内部 Hom と閉構造の単位・合成による豊穣。 -/
instance sSetInternalObject_enrichedCategory :
    EnrichedCategory SSet.{u} SSetInternalObject.{u} where
  Hom X Y := (ihom X.obj).obj Y.obj
  id X := MonoidalClosed.id X.obj
  comp X Y Z := MonoidalClosed.comp X.obj Y.obj Z.obj
  id_comp X Y := MonoidalClosed.id_comp X.obj Y.obj
  comp_id X Y := MonoidalClosed.comp_id X.obj Y.obj
  assoc W X Y Z := MonoidalClosed.assoc W.obj X.obj Y.obj Z.obj

/-- 元の通常射は、同じ閉内部 Hom の単位からの射に対応する。 -/
instance sSetInternalObject_simplicialCategory : SimplicialCategory SSetInternalObject.{u} where
  homEquiv {X Y} := curryHomEquiv' (X := X.obj) (Y := Y.obj)
  homEquiv_id X := curry'_id X.obj
  homEquiv_comp f g := curry'_comp (C := SSet.{u}) f g

/-- 豊穣だけを忘れると、同じ元の単体集合と通常射を得る。 -/
def sSetInternalObjectForget : SSetInternalObject.{u} ⥤ SSet.{u} where
  obj X := X.obj
  map f := f
  map_id _X := rfl
  map_comp _f _g := rfl

end SerrePositivity.KST.SConstruction
