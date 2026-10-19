module

public import SerrePositivity.KST.Spectra.PointedCotensorCoordinates
public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges
public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices

/-!
概要：点つき Hom に値を取る通常の族を、自由パラメータ cotensor 値の点つき射へ移す。
方針：座標同型の逆を族の頂点へ作用させ、元の familyMap で評価する。
規約：関数複体の全体の同型を使用。使われ方：段区間の自由区間座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates

/-- 元の通常の族を、自由パラメータ cotensor を値とする実際の点つき射へ移す。 -/
def family {K : SSet.{u}} {T E : PointedSimplicialSet.{u}}
    (a : K ⟶ (PointedObject.basedHom T E).right) :
    T ⟶ PointedObject.basedHom (PointedObject.adjoin K) E :=
  PointedMapping.familyMap T (PointedObject.basedHom (PointedObject.adjoin K) E)
    ((iso K T E).inv.app _ (ExponentialPaths.vertex a))

/-- 族の頂点を座標同型へ戻すと、元の通常の族の同じ頂点になる。 -/
lemma family_vertex {K : SSet.{u}} {T E : PointedSimplicialSet.{u}}
    (a : K ⟶ (PointedObject.basedHom T E).right) :
    (iso K T E).hom.app _ (PointedMapping.familyVertex (family a)) =
      ExponentialPaths.vertex a := by
  rw [family, PointedMapping.familyVertex_familyMap]
  change ((iso K T E).inv ≫ (iso K T E).hom).app _ (ExponentialPaths.vertex a) = _
  rw [Iso.inv_hom_id]
  rfl

/-- 自由パラメータの cotensor 値の射は、この全関数複体の座標の頂点で決まる。 -/
lemma ext {K : SSet.{u}} {T E : PointedSimplicialSet.{u}}
    {f g : T ⟶ PointedObject.basedHom (PointedObject.adjoin K) E}
    (h : (iso K T E).hom.app _ (PointedMapping.familyVertex f) =
      (iso K T E).hom.app _ (PointedMapping.familyVertex g)) : f = g := by
  apply (PointedMapping.familyVertexEquiv T _).injective
  exact ((iso K T E).app (Opposite.op ⦋0⦌)).toEquiv.injective h

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
