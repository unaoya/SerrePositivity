module

public import SerrePositivity.KST.Spectra.PointedCotensorFamilyNaturality
public import SerrePositivity.KST.Spectra.PointedBasedIntervalTraces

/-!
概要：通常の関数複体の実ホモトピーを、自由パラメータ cotensor 値の実区間へ移す。
方針：指数辺を座標同型の逆で移し、同じ区間を点つき Hom の辺として読む。
規約：ホモトピー全体を保持。使われ方：構造正方形の自由区間座標への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates
variable {K : SSet.{u}} {T E : PointedSimplicialSet.{u}}
  {a b : K ⟶ (PointedObject.basedHom T E).right} (H : SSet.Homotopy a b)

/-- 同じ実ホモトピーを、cotensor 値の二つの点つき射の実区間へ移す。 -/
def intervalOfHomotopy : PointedMapping.VerticalPath
    (PointedObject.toPoint (PointedObject.basedHom (PointedObject.adjoin K) E))
    (family a) (family b) :=
  PointedMapping.basedPathOfEdge (((ExponentialPaths.edge H).map (iso K T E).inv).ofEq
    (PointedMapping.familyVertex_familyMap T _ _).symm
    (PointedMapping.familyVertex_familyMap T _ _).symm)

/-- 移送後の実区間は、元の正方形の curry に同じ座標逆射を後合成したもの。 -/
lemma intervalOfHomotopy_path : (intervalOfHomotopy H).path = curry H.h ≫ (iso K T E).inv := by
  change SSet.yonedaEquiv.symm
    (((ExponentialPaths.edge H).map (iso K T E).inv).edge) = _
  rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp, ExponentialPaths.edge_path]

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
