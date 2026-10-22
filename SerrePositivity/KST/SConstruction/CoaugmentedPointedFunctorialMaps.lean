module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedMaps

/-! # 元の写した通常射と単位を保つ点つき関手
概要：元の基礎関手の射をそのまま使う点つき関手と、同じ単位の自然変換を与える。
方針：基礎射で恒等・合成・自然性を検出する。
規約：標準豊穣の通常射回収と同じ射を使う。使われ方：smash と suspension の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
variable (F : SSet.{u} ⥤ SSet.{u}) (η : 𝟭 SSet.{u} ⟶ F)

/-- 同じ写した通常の点つき射は恒等射を保つ。 -/
lemma coaugmentedPointedMap_id (X : PointedSSetObject.{u}) :
    coaugmentedPointedMap F η (𝟙 X) = 𝟙 (coaugmentedPointedObject F η X) := by
  apply Under.UnderMorphism.ext
  exact F.map_id X.obj.right

/-- 同じ写した通常の点つき射は合成を保つ。 -/
lemma coaugmentedPointedMap_comp {X Y Z : PointedSSetObject.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    coaugmentedPointedMap F η (f ≫ g) =
      coaugmentedPointedMap F η f ≫ coaugmentedPointedMap F η g := by
  apply Under.UnderMorphism.ext
  exact F.map_comp (show X.obj ⟶ Y.obj from f).right (show Y.obj ⟶ Z.obj from g).right

/-- 元の基礎関手の同じ実値・通常射からなる点つき関手。 -/
def coaugmentedPointedOrdinaryFunctor : PointedSSetObject.{u} ⥤ PointedSSetObject.{u} where
  obj := coaugmentedPointedObject F η
  map := coaugmentedPointedMap F η
  map_id := coaugmentedPointedMap_id F η
  map_comp := coaugmentedPointedMap_comp F η

/-- 元の同じ単位は、元の写した通常射について厳密に自然。 -/
lemma coaugmentedPointedUnit_naturality {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    coaugmentedPointedUnit F η X ≫ coaugmentedPointedMap F η f =
      f ≫ coaugmentedPointedUnit F η Y := by
  apply Under.UnderMorphism.ext
  exact (η.naturality (show X.obj ⟶ Y.obj from f).right).symm

end SerrePositivity.KST.SConstruction
