module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointNormalized
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedEndpointNormalization
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroTargetEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointVertexReflection

/-!
概要：零面の指定比較の両端を、元の二辺合成と長辺の全係数作用へ戻す。
方針：同じ実終点評価の既存の頂点等式を、fiber 持ち上げで実境界へ反映する。
規約：元の三射と全初点係数を保持する。
使われ方：零面の最後辺の指定比較正方形の両終点を固定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "p" => pointedSpaceProjection
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι p (coherentNerveVertex K)
local notation "j" => simplexPrismVertex 2 2 A
local notation "y" => coherentNerveVertex L
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor
  (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s))))
local notation "Q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor
  (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 0 s))))
local notation "R" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor
  (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 1 s))))

/-- 概要：元の二辺を順に作用させた全初点係数の実終点射。方針：全終点評価の頂点式を反映。
規約：元の三射と全係数を保持。使われ方：零面の最後辺の正規化。 -/
def spaceCompositionZeroCompositeMap : A ⟶ vertexFiber p y :=
  (P ≫ Q) ≫ pointedCoherentFiberComparison L

/-- 概要：元の長辺を作用させた全初点係数の実終点射。方針：全終点評価の頂点式を反映。
規約：元の三射と全係数を保持。使われ方：零面の最後辺の正規化。 -/
def spaceCompositionZeroTargetMap : A ⟶ vertexFiber p y :=
  R ≫ pointedCoherentFiberComparison L

/-- 概要：最大化側の同じ実終点は、元の二辺の合成作用そのもの。方針：全終点評価の頂点式を反映。
規約：元の三射と全係数を保持。使われ方：零面の最後辺の正規化。 -/
lemma spaceCompositionZeroCompositeMap_standard :
    j ≫ spaceSimplexPointedFamily M =
      spaceCompositionZeroCompositeMap s ≫ vertexFiberι p y := by
  apply (relativeExtensionFiberEndpoint_vertex_iff p β i v
    (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)
    (spaceSimplexPointedFamily M) (spaceSimplexPointedFamily_projection M)
    (spaceSimplexPointedFamily_firstVertex M) (spaceCompositionZeroCompositeMap s)).mp
  exact (spaceCompositionZeroEndpoint_source_eq_opposite_action s).trans
    (pointedOppositeTriangleAction_source_vertex s)

/-- 概要：零面側の同じ実終点は、元の長辺の作用そのもの。方針：全終点評価の頂点式を反映。
規約：元の三射と全係数を保持。使われ方：零面の最後辺の正規化。 -/
lemma spaceCompositionZeroTargetMap_zero :
    j ≫ spaceCompositionTetrahedronZeroFamily s =
      spaceCompositionZeroTargetMap s ≫ vertexFiberι p y := by
  apply (relativeExtensionFiberEndpoint_vertex_iff p β i v
    (spaceSimplexPointedFamily_boundary M) j y (spaceCompositionZeroEndpoint_base s)
    (spaceCompositionTetrahedronZeroFamily s) (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) (spaceCompositionZeroTargetMap s)).mp
  exact (spaceCompositionZeroEndpoint_target_eq_opposite_action s).trans
    (pointedOppositeTriangleAction_target_vertex s)

/-- 概要：実両端を正規化した零面の指定終点比較は元の反転精密化の作用。方針：全終点評価の頂点式を反映。
規約：元の三射と全係数を保持。使われ方：零面の最後辺の正規化。 -/
lemma spaceCompositionZeroTargetEndpointIso_heq_zero :
    HEq (spaceSimplexPointedFamilyEndpointIso M (spaceCompositionTetrahedronZeroFamily s)
      (spaceCompositionTetrahedronZeroFamily_projection s)
      (spaceCompositionTetrahedronZeroFamily_initial s) j y (spaceCompositionZeroEndpoint_base s)
      (spaceCompositionZeroCompositeMap s) (spaceCompositionZeroTargetMap s)
      (spaceCompositionZeroCompositeMap_standard s) (spaceCompositionZeroTargetMap_zero s))
        (pointedOppositeTriangleFunctorIso s) := by
  apply spaceSimplexPointedFamilyEndpointIso_heq_of_comparison_heq
  rw [← spaceCompositionTetrahedronZeroComparison_eq_family s]
  rw [← spaceCompositionZeroTargetEvaluation_eq_family s]
  exact spaceCompositionZeroTargetEvaluation_comparison_heq s

end SerrePositivity.InfinityCategories.F2
