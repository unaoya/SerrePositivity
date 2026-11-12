module
public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-! # 点つき自然性の指定辺の前後合成
概要：合成入力の自然性に現れる二つの辺を、同じ三つの頂点の間へ移す。
方針：写像空間の前後合成と元の関手の厳密な合成保存を使う。
規約：入力した辺の像の一単体を保持する。
使われ方：構造射の二入力の自然性三角形の外側の辺を固定する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 最初の自然性の辺を後合成し、合成入力の源と中間の頂点の間へ移す。 -/
def pointedNaturalityCompositionFirstEdge {J : Type v} [Category J]
    (B L : J ⥤ PointedSimplicialSet.{u}) {X Y Z : J} (f : X ⟶ Y) (g : Y ⟶ Z)
    (sX : B.obj X ⟶ L.obj X) (sY : B.obj Y ⟶ L.obj Y)
    (e : (PointedObject.basedHom (B.obj X) (L.obj Y)).right.Edge
      (familyVertex (sX ≫ L.map f)) (familyVertex (B.map f ≫ sY))) :
    (PointedObject.basedHom (B.obj X) (L.obj Z)).right.Edge
      (familyVertex (sX ≫ L.map (f ≫ g))) (familyVertex (B.map f ≫ sY ≫ L.map g)) :=
  (e.map (PointedObject.basedHomMap (B.obj X) (L.map g)).right).ofEq
    ((familyVertex_post (sX ≫ L.map f) (L.map g)).trans
      (congrArg familyVertex (by rw [Category.assoc, ← L.map_comp])))
    ((familyVertex_post (B.map f ≫ sY) (L.map g)).trans
      (congrArg familyVertex (Category.assoc _ _ _)))

/-- 後の自然性の辺を前合成し、同じ中間頂点と合成入力の標的の間へ移す。 -/
def pointedNaturalityCompositionSecondEdge {J : Type v} [Category J]
    (B L : J ⥤ PointedSimplicialSet.{u}) {X Y Z : J} (f : X ⟶ Y) (g : Y ⟶ Z)
    (sY : B.obj Y ⟶ L.obj Y) (sZ : B.obj Z ⟶ L.obj Z)
    (e : (PointedObject.basedHom (B.obj Y) (L.obj Z)).right.Edge
      (familyVertex (sY ≫ L.map g)) (familyVertex (B.map g ≫ sZ))) :
    (PointedObject.basedHom (B.obj X) (L.obj Z)).right.Edge
      (familyVertex (B.map f ≫ sY ≫ L.map g)) (familyVertex (B.map (f ≫ g) ≫ sZ)) :=
  (e.map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (B.map f) (L.obj Z)).right).ofEq
    (familyVertex_pre (B.map f) (sY ≫ L.map g))
    ((familyVertex_pre (B.map f) (B.map g ≫ sZ)).trans
      (congrArg familyVertex (by rw [← Category.assoc, ← B.map_comp])))

end SerrePositivity.KST.SConstruction
