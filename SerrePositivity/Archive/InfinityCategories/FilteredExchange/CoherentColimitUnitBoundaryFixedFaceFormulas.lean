module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitBoundaryComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTransferredPostEdges

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

/-- 面 012 の元の指定比較は、共通の辺 01・12・02 の指定比較で厳密に表示される。 -/
lemma CoherentColimitUnitTetrahedronBoundary.face012_comparison :
    (functorTriangleSequentialPostComparison D.triangle012 p).app x₀ =
      D.comparison02 ≪≫ D.comparison12.symm ≪≫
        VertexIso.map D.comparison01.symm (functorHomotopyRelativePost D.edge12 p) :=
  D.w012.sequentialPostComparison_app_eq_threeEdges rfl

/-- 面 013 の元の指定比較は、同じ共通頂点と辺 01・13・03 の指定比較で厳密に表示される。 -/
lemma CoherentColimitUnitTetrahedronBoundary.face013_comparison :
    (functorTriangleSequentialPostComparison D.triangle013 p).app x₀ =
      D.comparison03 ≪≫ D.comparison13.symm ≪≫
        VertexIso.map D.comparison01.symm (functorHomotopyRelativePost D.edge13 p) := by
  refine D.w013.sequentialPostComparison_app_eq_transferredEdges rfl D.x1 D.x3
    D.comparison01 D.comparison13 D.comparison03 D.middle013_vertex rfl ?_ ?_ ?_
  · exact functorHomotopySourcePostIso_heq_shared_prism D.edge01 p _ _ rfl rfl _ _
      (coherentColimitUnitSharedFirstEdge_prism B T k D.triangle013 D.triangle012
        D.face013 D.face012)
  · exact D.comparison13_heq.symm
  · rfl

/-- 面 023 の元の指定比較は、同じ共通頂点と辺 02・23・03 の指定比較で厳密に表示される。 -/
lemma CoherentColimitUnitTetrahedronBoundary.face023_comparison :
    (functorTriangleSequentialPostComparison D.triangle023 p).app x₀ =
      D.comparison03 ≪≫ D.comparison23.symm ≪≫
        VertexIso.map D.comparison02.symm (functorHomotopyRelativePost D.edge23 p) := by
  refine D.w023.sequentialPostComparison_app_eq_transferredEdges rfl D.x2 D.x3
    D.comparison02 D.comparison23 D.comparison03 D.middle023_vertex D.endpoint023_vertex ?_ ?_ ?_
  · exact functorHomotopySourcePostIso_heq_shared_prism D.edge02 p _ _ rfl rfl _ _
      (coherentColimitUnitSharedInitialDiagonalEdge_prism B T k D.triangle023 D.triangle012
        D.face023 D.face012)
  · exact D.comparison23_heq.symm
  · exact functorHomotopySourcePostIso_heq_shared_prism D.edge03 p _ _ rfl rfl _ _
      (coherentColimitUnitSharedLongEdge_prism B T k D.triangle023 D.triangle013
        D.face023 D.face013)

end SerrePositivity.InfinityCategories.F2
