module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleEdgeEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：同じ全三角形比較の辺像・全終点像を、元の二実延長の頂点の表示で保持する。
方針：元の端点評価の頂点公式と明示した等号同型を使う。
規約：元の指定値を再選択しない。使われ方：右辺の指定自然性の終点像との同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)
  (hi : s ≫ leftUnstraighteningProjection F = p)

/-- 指定辺比較の端点表示を揃えても、元の全三角形比較の辺像の値を保持する。 -/
lemma FunctorTrianglePointedWitness.prismComparison_heq_edge {Q R : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy Q R) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h) :
    HEq (w.prismComparison H i hFace hi) (w.edgeComparison H i hFace hi) :=
  iso_endpoints_heq _ (congrArg SSet.HomotopyCategory.mk (w.edgeMap_vertex H i hFace w))
    (congrArg SSet.HomotopyCategory.mk
      (w.edgeMap_vertex H i hFace (functorTrianglePointedCanonicalWitness T p s hi)))

/-- 元の全終点評価は、元の同じ実終点射の頂点を厳密に返す。 -/
lemma FunctorTrianglePointedWitness.endpointMap_vertex (w' : FunctorTrianglePointedWitness T p s) :
    w.endpointMap.app _ (w.point w') =
      relativeFunctorVertex (leftUnstraighteningProjection J) p
        w'.endpoint w'.endpoint_projection :=
  relativeFunctorExtensionEndpoint_vertex pointedSpaceProjection
    ((Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram) (scaffoldFirstVertex 2 ▷ C)
    (snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F) w.start_projection
    (simplexPrismVertex 2 2 C) J p (functorTrianglePrism_terminal_base T p)
    w'.prism w'.projection w'.start w'.endpoint w'.endpoint_projection w'.endpoint_pointed

/-- 元の同じ全三角形比較を、元の実終点射の表示へ揃えて評価した値。 -/
def FunctorTrianglePointedWitness.endpointComparison :=
  vertexIsoOfEq (VertexIso.map (w.comparison hi) w.endpointMap)
    (w.endpointMap_vertex w)
    (w.endpointMap_vertex (functorTrianglePointedCanonicalWitness T p s hi))

end SerrePositivity.InfinityCategories.F2
