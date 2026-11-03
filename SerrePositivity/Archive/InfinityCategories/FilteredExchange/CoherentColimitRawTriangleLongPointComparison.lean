module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTriangleLongPrismData

/-!
概要：指定二実辺を持つ任意の全三角形の長辺を、元の同じ長辺普遍 prism と比較する。
方針：元の実始点・終点・底を回収し、同じ相対延長の指定比較へ入力する。
規約：全持ち上げと指定値を保持。使われ方：全長辺比較の元の二成分への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (W : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (g : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))
  (Y : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hY : Y ≫ pointedSpaceProjection = fst (Δ[2] : SSet.{u + 1}) K ≫
    T.diagram ≫ coherentColimitFunctor B)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ Y = W)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ Y = coherentColimitRawTransportPointPrism B b g)

/-- 任意の元の二辺固定三角形の長辺から、同じ元の普遍長辺への指定比較。 -/
def coherentColimitRawTriangleLongPointComparison :
    FunctorIso (g ≫ coherentColimitRawFiberTransport B b)
      (f ≫ coherentColimitRawFiberTransport B d) :=
  relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection
    (fst (Δ[1] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B d).edge) (prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K)
    (f ≫ vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (coherentColimitRawFirstChoice_initial_base B d f) (prismEndpoint 1 K) _
    (coherentColimitRawFirstChoice_final_base B d f)
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Y) (coherentColimitRawTransportPointPrism B d f)
    (coherentColimitRawTriangleLong_projection B T Y hY)
    (coherentColimitRawTransportPointPrism_projection B d f)
    (coherentColimitRawTriangleLong_start B f W hs Y hfirst)
    (coherentColimitRawTransportPointPrism_start B d f) _ _
    (coherentColimitRawTriangleLong_finish B g Y hlast)
    (coherentColimitRawTransportPointPrism_finish B d f)

end SerrePositivity.InfinityCategories.F2
