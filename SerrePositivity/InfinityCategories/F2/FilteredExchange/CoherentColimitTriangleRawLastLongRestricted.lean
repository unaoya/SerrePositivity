module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitTriangleRawLastLongTransport

/-!
概要：元の指定三角形と raw 普遍最終辺の持ち上げを、長辺と最後辺で同時に比較する。
方針：同じ最初辺を固定した全比較を二つの実辺へ制限する。
規約：元の二単体・全係数・実両端を保持。使われ方：長辺残余と一点輸送比較の照合。
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
  {F G J : Functor.obj SSet.uliftFunctor.{u + 1, u} B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "CF" => SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F))
local notation "CG" => SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G))
local notation "E" => leftUnstraightening (coherentColimitRawConstantDiagram B F)
local notation "ma" => Subtype.val
  (leftUnstraighteningMappingVertexMap _ _ (coherentVertexOfHomotopy ca))
local notation "H₀₁" => functorHomotopyPointedPrism ca (𝟙 E)
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (ma ≫ coherentColimitRawConstantFiberProjection B G)
local notation "β" => (Δ[2] ◁ leftUnstraighteningProjection
  (coherentColimitRawConstantDiagram B F)) ≫
  functorSimplexDiagram (FunctorCompositionTriangle.diagram (coherentColimitConstantTriangle B T))

local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "mb" => Subtype.val
  (leftUnstraighteningMappingVertexMap _ _ (coherentVertexOfHomotopy cb))
local notation "W₀" => functorTrianglePointedLift (coherentColimitConstantTriangle B T)
local notation "j" => prismEndpoint 1 E ≫ (stdSimplex.δ (1 : Fin 3) ▷ E)
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone J)

local notation "W₁" => coherentColimitTriangleRawLastPrism B T
local notation "g₀" => ma ≫ mb ≫ coherentColimitRawConstantFiberProjection B J
local notation "g₁" => (ma ≫ coherentColimitRawConstantFiberProjection B G) ≫
  coherentColimitRawFiberTransport B b

local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "w" => coherentColimitConstantTriangleLongTransport B T
local notation "U" => coherentColimitTriangleRawLastLongTransport B T
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 E) (SSet.const l)

/-- 元の二つの全長辺輸送の一点制限は、同じ全三角形の元の長辺比較そのもの。 -/
lemma coherentColimitTriangleRawLastLongComparison_heq_long_restricted :
    HEq (coherentColimitTriangleRawLastLongComparison B T)
      (fiberTransportRestrictedPrismComparison pointedSpaceProjection P
        (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s) := by
  apply relativeFiberWitness_heq_restrictedPrism
  · rw [Category.assoc, functorTrianglePointedLift_projection]
  · rw [Category.assoc, coherentColimitTriangleRawLastPrism_projection]
  · rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
      coherentColimitTriangleRawLast_original_first]
  · rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
      coherentColimitTriangleRawLastPrism_first]
  · simpa only [coherentColimitRawConstantDiagram, Category.assoc] using
      coherentColimitTriangleRawLast_original_terminal B T
  · simpa only [coherentColimitRawConstantDiagram, Category.assoc] using
      coherentColimitTriangleRawLastPrism_terminal B T
  · exact (coherentColimitConstantTriangleLongTransport_point_prism B T).symm
  · exact (coherentColimitTriangleRawLastLongTransport_point_prism B T l).symm

/-- 元の二長辺輸送の endpointIso の一点値は、同じ元の全長辺比較と値まで一致する。 -/
lemma coherentColimitTriangleRawLastLongComparison_heq_long_endpointIso :
    HEq (coherentColimitTriangleRawLastLongComparison B T)
      (FunctorIso.precomp (FiberTransportFamily.endpointIso pointedSpaceProjection P
        (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U) s) :=
  (coherentColimitTriangleRawLastLongComparison_heq_long_restricted B T).trans
    (heq_of_eq (fiberTransportRestrictedPrismComparison_eq_endpointIso pointedSpaceProjection P
      (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s))

/-- 元の二長辺輸送の指定比較の一点値は、元の最後辺の指定一点比較の同じ前合成。 -/
lemma coherentColimitTriangleRawLastLongEndpointIso_heq_point :
    HEq (FunctorIso.precomp (FiberTransportFamily.endpointIso pointedSpaceProjection P
      (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U) s)
      ((coherentColimitConstantTransportPointIso B b).precomp ma) :=
  (coherentColimitTriangleRawLastLongComparison_heq_long_endpointIso B T).symm.trans
    (coherentColimitTriangleRawLastLongComparison_heq_point B T)

end SerrePositivity.InfinityCategories.F2
