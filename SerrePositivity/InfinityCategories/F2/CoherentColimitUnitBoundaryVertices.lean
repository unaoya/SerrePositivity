module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitBoundaryWitnesses

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

/-- 面 013 の実中間点は、同じ全三単体の共通頂点一。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle013 : D.w013.middle = D.source1 :=
  coherentColimitUnitSharedFirstEdge_endpoint B T k D.triangle013 D.triangle012
    D.face013 D.face012

/-- 面 023 の実中間点は、同じ全三単体の共通頂点二。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle023 : D.w023.middle = D.source2 :=
  coherentColimitUnitSharedInitialDiagonalEdge_endpoint B T k D.triangle023 D.triangle012
    D.face023 D.face012

/-- 面 023 の実終点は、同じ全三単体の共通頂点三。 -/
lemma CoherentColimitUnitTetrahedronBoundary.endpoint023 : D.w023.endpoint = D.source3 :=
  coherentColimitUnitSharedLongEdge_endpoint B T k D.triangle023 D.triangle013
    D.face023 D.face013

/-- 第零面の実始点は、同じ全三単体の共通頂点一。 -/
lemma CoherentColimitUnitTetrahedronBoundary.initial123 :
    coherentColimitUnitPointedFirstEdgeEndpoint B T k D.edge01 D.firstEdge = D.source1 :=
  (coherentColimitUnitSharedMiddleEdge_source B T k D.triangle012 D.triangle123
    D.firstEdge D.face012 D.face123).symm

/-- 第零面の実中間点は、同じ全三単体の共通頂点二。 -/
lemma CoherentColimitUnitTetrahedronBoundary.middle123 : D.w123.middle = D.source2 :=
  (coherentColimitUnitSharedMiddleEdge_endpoint B T k D.triangle012 D.triangle123
    D.firstEdge D.face012 D.face123).symm

/-- 第零面の実終点は、同じ全三単体の共通頂点三。 -/
lemma CoherentColimitUnitTetrahedronBoundary.endpoint123 : D.w123.endpoint = D.source3 :=
  (coherentColimitUnitSharedMiddleDiagonalEdge_endpoint B T k D.triangle013 D.triangle123
    D.firstEdge D.face013 D.face123).symm

end SerrePositivity.InfinityCategories.F2
