module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitBoundaryRelativeVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySharedPostIso

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

local notation "x₀" => relativeFunctorVertex (leftUnstraighteningProjection F) p
  (fst (leftUnstraightening F) K) rfl

/-- 共通の辺 01 の元の指定比較。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison01 :
    VertexIso ((functorHomotopyRelativePost D.edge01 p).app _ x₀) D.x1 :=
  functorHomotopySourcePostIso D.edge01 p (fst (leftUnstraightening F) K) rfl D.w012.firstWitness

/-- 共通の辺 02 の元の指定比較。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison02 :
    VertexIso ((functorHomotopyRelativePost D.edge02 p).app _ x₀) D.x2 :=
  functorHomotopySourcePostIso D.edge02 p (fst (leftUnstraightening F) K) rfl D.w012.longWitness

/-- 共通の辺 12 の元の指定比較。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison12 :
    VertexIso ((functorHomotopyRelativePost D.edge12 p).app _ D.x1) D.x2 :=
  functorHomotopySourcePostIso D.edge12 p D.source1 D.source1_over D.w012.secondWitness

/-- 共通の辺 03 の元の指定比較。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison03 :
    VertexIso ((functorHomotopyRelativePost D.edge03 p).app _ x₀) D.x3 :=
  functorHomotopySourcePostIso D.edge03 p (fst (leftUnstraightening F) K) rfl D.w013.longWitness

/-- 共通の辺 13 の元の指定比較を、同じ頂点一・三の表示で保持する。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison13 :
    VertexIso ((functorHomotopyRelativePost D.edge13 p).app _ D.x1) D.x3 :=
  vertexIsoOfEq
    (functorHomotopySourcePostIso D.edge13 p D.w013.middle
      D.w013.middle_projection D.w013.secondWitness)
    (congrArg (fun v => (functorHomotopyRelativePost D.edge13 p).app (Opposite.op ⦋0⦌) v)
      D.middle013_vertex) rfl

/-- 共通の辺 23 の元の指定比較を、同じ頂点二・三の表示で保持する。 -/
def CoherentColimitUnitTetrahedronBoundary.comparison23 :
    VertexIso ((functorHomotopyRelativePost D.edge23 p).app _ D.x2) D.x3 :=
  vertexIsoOfEq
    (functorHomotopySourcePostIso D.edge23 p D.w023.middle
      D.w023.middle_projection D.w023.secondWitness)
    (congrArg (fun v => (functorHomotopyRelativePost D.edge23 p).app (Opposite.op ⦋0⦌) v)
      D.middle023_vertex) D.endpoint023_vertex

/-- 共通頂点の表示へ移しても、元の同じ辺 13 の指定値を保持する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.comparison13_heq :
    HEq D.comparison13 (functorHomotopySourcePostIso D.edge13 p D.w013.middle
      D.w013.middle_projection D.w013.secondWitness) :=
  vertexIsoOfEq_heq _
    (congrArg (fun v => (functorHomotopyRelativePost D.edge13 p).app (Opposite.op ⦋0⦌) v)
      D.middle013_vertex) rfl

/-- 共通頂点の表示へ移しても、元の同じ辺 23 の指定値を保持する。 -/
lemma CoherentColimitUnitTetrahedronBoundary.comparison23_heq :
    HEq D.comparison23 (functorHomotopySourcePostIso D.edge23 p D.w023.middle
      D.w023.middle_projection D.w023.secondWitness) :=
  vertexIsoOfEq_heq _
    (congrArg (fun v => (functorHomotopyRelativePost D.edge23 p).app (Opposite.op ⦋0⦌) v)
      D.middle023_vertex) D.endpoint023_vertex

end SerrePositivity.InfinityCategories.F2
