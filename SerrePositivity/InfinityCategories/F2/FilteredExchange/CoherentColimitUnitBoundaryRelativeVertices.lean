module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitBoundaryVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyRelativePost

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

/-- 元の共通頂点一を、元の全底を固定する相対関手空間の頂点として保持する。 -/
def CoherentColimitUnitTetrahedronBoundary.x1 :=
  relativeFunctorVertex (leftUnstraighteningProjection D.vertex1) p D.source1 D.source1_over

/-- 元の共通頂点二を、元の全底を固定する相対関手空間の頂点として保持する。 -/
def CoherentColimitUnitTetrahedronBoundary.x2 :=
  relativeFunctorVertex (leftUnstraighteningProjection D.vertex2) p D.source2 D.source2_over

/-- 元の共通頂点三を、元の全底を固定する相対関手空間の頂点として保持する。 -/
def CoherentColimitUnitTetrahedronBoundary.x3 :=
  relativeFunctorVertex (leftUnstraighteningProjection D.vertex3) p D.source3 D.source3_over

/-- 元の middle013 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle013_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex1) p
      (D.w013.middle) (D.w013.middle_projection) = D.x1 := by
  apply Subtype.ext
  exact congrArg functorVertex D.middle013

/-- 元の middle023 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle023_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex2) p
      (D.w023.middle) (D.w023.middle_projection) = D.x2 := by
  apply Subtype.ext
  exact congrArg functorVertex D.middle023

/-- 元の endpoint023 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.endpoint023_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex3) p
      (D.w023.endpoint) (D.w023.endpoint_projection) = D.x3 := by
  apply Subtype.ext
  exact congrArg functorVertex D.endpoint023

/-- 元の initial123 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.initial123_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex1) p
      (coherentColimitUnitPointedFirstEdgeEndpoint B T k D.edge01 D.firstEdge)
        (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k D.edge01 D.firstEdge) =
        D.x1 := by
  apply Subtype.ext
  exact congrArg functorVertex D.initial123

/-- 元の middle123 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle123_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex2) p
      (D.w123.middle) (D.w123.middle_projection) = D.x2 := by
  apply Subtype.ext
  exact congrArg functorVertex D.middle123

/-- 元の endpoint123 の相対頂点は、同じ全三単体の共通頂点の表示に厳密に一致する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.endpoint123_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection D.vertex3) p
      (D.w123.endpoint) (D.w123.endpoint_projection) = D.x3 := by
  apply Subtype.ext
  exact congrArg functorVertex D.endpoint123

end SerrePositivity.InfinityCategories.F2
