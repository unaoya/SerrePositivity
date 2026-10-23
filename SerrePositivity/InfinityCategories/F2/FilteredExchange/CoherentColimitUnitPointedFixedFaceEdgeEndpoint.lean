module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceEndpointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyEdgeEndpoint

/-!
概要：三証拠の中間の長辺比較は、構成済みの元の native 合成への終点比較と値まで一致。
方針：長辺制限先の可縮性と終点評価の厳密な因子分解で、元の全族比較へ戻す。
規約：元の指定同型を保持。使われ方：三証拠の合成式の native 比較側の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS
local notation "a₂" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "hEnd" => coherentColimitUnitPointedFixedFaceBase_endpoint B T k j hj S hS

/-- 元の固定面の長辺・最後の辺の指定比較は、終点で同じ native 合成比較になる。 -/
lemma coherentColimitUnitPointedFixedFaceEndpointIso_heq_edge (i : Fin 3) (hi : i ≠ 2) :
    HEq (coherentColimitUnitPointedFixedFaceEndpointIso B T k j hj S hS)
      (VertexIso.map (coherentColimitUnitPointedFixedFaceEdgeComparison B T k j hj S hS i)
        (pointedTriangleFamilyEdgeEndpointMap D Q₂ a₂ hEnd i hi)) := by
  let e := coherentColimitUnitPointedFixedFaceOriginalComparison B T k j hj S hS
  have hc := vertexIso_map_comp e (pointedTriangleFamilyEdgeMap D i)
    (pointedTriangleFamilyEdgeEndpointMap D Q₂ a₂ hEnd i hi)
  have heq := vertexIso_map_heq e (pointedTriangleFamilyEdgeEndpoint_factor D Q₂ a₂ hEnd i hi)
  exact (coherentColimitUnitPointedFixedFaceEndpointIso_heq_map B T k j hj S hS).trans
    ((heq_of_eq hc).trans heq).symm

end SerrePositivity.InfinityCategories.F2
