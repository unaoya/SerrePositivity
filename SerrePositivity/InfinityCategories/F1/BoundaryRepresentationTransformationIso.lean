module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessBoundaryDiagram
public import SerrePositivity.InfinityCategories.F1.EndpointPairTransformationVertices

/-!
概要：小さい全空間の共通両端を保つ二つの表現は変換空間内で同型な変換を与える。
方針：境界固定の表現の可縮 fiber を固定図式空間と変換空間へ順に写す。
規約：単なる区間全体の関手同型でなく固定端点の変換の空間内で比較する。
使われ方：写像空間比較の左逆の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：共通境界を持つ二表現の区間図式は固定端点の変換空間内で同型。
方針：可縮 fiber の同型を境界図式の空間へ写し変換空間へ curry する。
規約：全空間のみ各次数で小さく、底の小ささは不要。
使われ方：元の変換と collage から復元した変換の比較。 -/
def smallBoundaryRepresentation_transformationIso {E D B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] (r : E ⟶ (Δ[1] : SSet.{u + 1}) ⊗ B)
    [LeftFibration r] (s : D ⟶ joinEndpointDiagram B B) [LeftFibration s]
    (e : D ⟶ E) (hp : IsPullback e s r (prismEndpointPair B))
    (F G : B ⟶ SpaceInfinity.{u}) (S : LeftTransportRepresentation s)
    (hS : S.diagram = joinEndpointDesc F G) (R T : LeftTransportRepresentation r)
    (hR : R.cartesianRestrict e (prismEndpointPair B) hp = S)
    (hT : T.cartesianRestrict e (prismEndpointPair B) hp = S)
    (hr₀ : prismEndpoint 0 B ≫ R.diagram = F) (hr₁ : prismEndpoint 1 B ≫ R.diagram = G)
    (ht₀ : prismEndpoint 0 B ≫ T.diagram = F) (ht₁ : prismEndpoint 1 B ≫ T.diagram = G) :
    VertexIso (X := leftUnstraighteningTransformationSpace F G)
      (intervalMappingVertexOfEdge (functorEdgeFromPrism R.diagram hr₀ hr₁))
      (intervalMappingVertexOfEdge (functorEdgeFromPrism T.diagram ht₀ ht₁)) := by
  let a : Arrow.mk s ⟶ Arrow.mk r := Arrow.homMk e (prismEndpointPair B) hp.w
  have : LeftFibration (Arrow.mk s).hom := by change LeftFibration s; infer_instance
  have : LeftFibration (Arrow.mk r).hom := by change LeftFibration r; infer_instance
  have : ∀ n, Small.{u} ((Arrow.mk r).left.obj n) := by
    change ∀ n, Small.{u} (E.obj n); infer_instance
  have : Mono a.right := by change Mono (prismEndpointPair B); infer_instance
  have hi := smallTransportRepresentation_fixedDiagramIso a hp S R T hR hT
  change VertexIso
    (fixedDiagramVertex (prismEndpointPair B) S.diagram R.diagram
      (congrArg LeftTransportRepresentation.diagram hR))
    (fixedDiagramVertex (prismEndpointPair B) S.diagram T.diagram
      (congrArg LeftTransportRepresentation.diagram hT)) at hi
  have hi' := VertexIso.map hi (eqToHom (congrArg
    (fun d ↦ vertexFiber ((pre (prismEndpointPair B)).app SpaceInfinity) (functorVertex d)) hS))
  rw [fixedDiagramVertex_transport (prismEndpointPair B) hS,
    fixedDiagramVertex_transport (prismEndpointPair B) hS] at hi'
  have hv := VertexIso.map hi' (endpointPairDiagramTransformationMap F G)
  have hdR : prismEndpointPair B ≫ R.diagram = joinEndpointDesc F G :=
    (congrArg LeftTransportRepresentation.diagram hR).trans hS
  have hdT : prismEndpointPair B ≫ T.diagram = joinEndpointDesc F G :=
    (congrArg LeftTransportRepresentation.diagram hT).trans hS
  have er := endpointPairDiagramTransformationMap_vertex F G R.diagram hr₀ hr₁ hdR
  have et := endpointPairDiagramTransformationMap_vertex F G T.diagram ht₀ ht₁ hdT
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk er)).symm ≪≫ hv ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk et)

end SerrePositivity.InfinityCategories
