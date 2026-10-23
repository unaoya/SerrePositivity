module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitBoundaryCommonZeroFace
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleTransferredPostEdges

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

/-- 第零面の元の第一辺の指定値は、共通の辺 12 の指定値そのもの。 -/
lemma CoherentColimitUnitTetrahedronBoundary.first123_comparison_heq :
    HEq (functorHomotopySourcePostIso D.edge12 p D.source1 D.source1_over
      D.w123Common.firstWitness) D.comparison12 :=
  functorHomotopySourcePostIso_heq_shared_prism D.edge12 p _ _ D.source1_over D.source1_over _ _
    (coherentColimitUnitSharedMiddleEdge_prism B T k D.triangle012 D.triangle123
      D.firstEdge D.face012 D.face123).symm

/-- 第零面の元の第二辺の指定値は、共通の辺 23 の指定値そのもの。 -/
lemma CoherentColimitUnitTetrahedronBoundary.second123_comparison_heq :
    HEq (functorHomotopySourcePostIso D.edge23 p D.w123Common.middle
      D.w123Common.middle_projection D.w123Common.secondWitness) D.comparison23 := by
  have h := functorHomotopySourcePostIso_heq_shared_prism D.edge23 p _ _
    D.w123Common.middle_projection D.w023.middle_projection D.w123Common.secondWitness
    D.w023.secondWitness (coherentColimitUnitSharedLastEdge_prism B T k D.triangle023
      D.triangle123 D.firstEdge D.face023 D.face123).symm
  exact h.trans D.comparison23_heq.symm

/-- 第零面の元の長辺の指定値は、共通の辺 13 の指定値そのもの。 -/
lemma CoherentColimitUnitTetrahedronBoundary.long123_comparison_heq :
    HEq (functorHomotopySourcePostIso D.edge13 p D.source1 D.source1_over
      D.w123Common.longWitness) D.comparison13 := by
  have h := functorHomotopySourcePostIso_heq_shared_prism D.edge13 p _ _ D.source1_over
    D.w013.middle_projection D.w123Common.longWitness D.w013.secondWitness
    (coherentColimitUnitSharedMiddleDiagonalEdge_prism B T k D.triangle013 D.triangle123
      D.firstEdge D.face013 D.face123).symm
  exact h.trans D.comparison13_heq.symm

/-- 第零面の指定比較も、同じ共通頂点と辺 12・23・13 の指定比較で厳密に表示される。 -/
lemma CoherentColimitUnitTetrahedronBoundary.face123_comparison :
    (functorTriangleSequentialPostComparison D.triangle123 p).app D.x1 =
      D.comparison13 ≪≫ D.comparison23.symm ≪≫
        VertexIso.map D.comparison12.symm (functorHomotopyRelativePost D.edge23 p) := by
  exact D.w123Common.sequentialPostComparison_app_eq_transferredEdges D.source1_over D.x2 D.x3
    D.comparison12 D.comparison23 D.comparison13 D.middle123Common_vertex D.endpoint123Common_vertex
    D.first123_comparison_heq D.second123_comparison_heq D.long123_comparison_heq

end SerrePositivity.InfinityCategories.F2
