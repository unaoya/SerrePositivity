module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceEdgeEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceEndpointComparison

/-!
概要：元の三角形の長辺・最後の辺の指定比較を終点で読むと、同じ native 合成比較となる。
方針：一つの全族比較の像の合成則と、厳密な終点評価の因子分解を使う。
規約：指定同型の値を保持。使われ方：六面の比較の三関係を元の合成比較へ接続。
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
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)

/-- 同じ第零面の二辺の指定比較は、終点で同じ元の native 合成比較へ厳密に揃う。 -/
lemma coherentColimitUnitZeroFaceEndpointIso_heq_edge (j : Fin 3) (hj : j ≠ 2) :
    HEq (coherentColimitUnitZeroFaceEndpointIso B T k H he S hS)
      (VertexIso.map (coherentColimitUnitZeroFaceEdgeComparison B T k H he S hS j)
        (coherentColimitUnitZeroFaceEdgeEndpointMap B T k H he S hS j hj)) := by
  let e := coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS
  have hc := vertexIso_map_comp e
    (pointedTriangleFamilyEdgeMap (coherentColimitUnitPointedZeroFaceFamily B T k) j)
    (coherentColimitUnitZeroFaceEdgeEndpointMap B T k H he S hS j hj)
  have heq := vertexIso_map_heq e
    (coherentColimitUnitZeroFaceEdgeEndpoint_factor B T k H he S hS j hj)
  exact (coherentColimitUnitZeroFaceEndpointIso_heq_map B T k H he S hS).trans
    ((heq_of_eq hc).trans heq).symm

end SerrePositivity.InfinityCategories.F2
