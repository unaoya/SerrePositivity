module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitBoundaryComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleWitnessSourceTransport

/-!
概要：元の四面の全実中間点・全実終点を、元の全三単体の共通頂点へ厳密に同定する。
方針：六共有辺の実始点・実終点の等式を同じ四面へ適用する。
規約：全係数と底の射影を保持。使われ方：四面の式を同じ六比較へ正規化する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle l r d} {k : Fin 3}
  (D : CoherentColimitUnitTetrahedronBoundary B T k)

local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F

/-- 元の第零面の始点だけを共通頂点一へ揃えた、同じ全実三角形。 -/
def CoherentColimitUnitTetrahedronBoundary.w123Common := D.w123.withSource D.initial123

/-- 始点の表示変更後も、元の第零面の全実中間点は同じ共通頂点二。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle123Common_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex2) p
      D.w123Common.middle D.w123Common.middle_projection = D.x2 := D.middle123_vertex

/-- 始点の表示変更後も、元の第零面の全実終点は同じ共通頂点三。 -/
lemma CoherentColimitUnitTetrahedronBoundary.endpoint123Common_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex3) p
      D.w123Common.endpoint D.w123Common.endpoint_projection = D.x3 := D.endpoint123_vertex

end SerrePositivity.InfinityCategories.F2
