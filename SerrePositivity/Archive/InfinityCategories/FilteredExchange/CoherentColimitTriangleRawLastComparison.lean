module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitTriangleRawLastData

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
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

/-- 同じ元の長辺と全係数上の raw 普遍最終辺による長辺の指定比較。 -/
def coherentColimitTriangleRawLastLongComparison : FunctorIso g₀ g₁ :=
  triangleFirstEdgeLongFiberComparison pointedSpaceProjection β H₀₁
    (coherentColimitTriangleRawLast_first_base B T) z
    (coherentColimitTriangleRawLast_terminal_base B T) W₀ W₁
    (functorTrianglePointedLift_projection (coherentColimitConstantTriangle B T))
    (coherentColimitTriangleRawLastPrism_projection B T)
    (coherentColimitTriangleRawLast_original_first B T)
    (coherentColimitTriangleRawLastPrism_first B T) g₀ g₁
    (coherentColimitTriangleRawLast_original_terminal B T)
    (coherentColimitTriangleRawLastPrism_terminal B T)

/-- 同じ元の最後辺と指定点の raw 普遍輸送との指定比較。 -/
def coherentColimitTriangleRawLastLastComparison : FunctorIso g₀ g₁ :=
  triangleFirstEdgeLastFiberComparison pointedSpaceProjection β H₀₁
    (coherentColimitTriangleRawLast_first_base B T) z
    (coherentColimitTriangleRawLast_terminal_base B T) W₀ W₁
    (functorTrianglePointedLift_projection (coherentColimitConstantTriangle B T))
    (coherentColimitTriangleRawLastPrism_projection B T)
    (coherentColimitTriangleRawLast_original_first B T)
    (coherentColimitTriangleRawLastPrism_first B T) g₀ g₁
    (coherentColimitTriangleRawLast_original_terminal B T)
    (coherentColimitTriangleRawLastPrism_terminal B T)

/-- 元の長辺の指定比較は、同じ全三角形の最後辺の指定比較と値まで厳密に一致する。 -/
lemma coherentColimitTriangleRawLastLongComparison_eq_last :
    coherentColimitTriangleRawLastLongComparison B T =
      coherentColimitTriangleRawLastLastComparison B T := by
  exact triangleFirstEdgeLongFiberComparison_eq_last pointedSpaceProjection β H₀₁
    (coherentColimitTriangleRawLast_first_base B T) z
    (coherentColimitTriangleRawLast_terminal_base B T) W₀ W₁
    (functorTrianglePointedLift_projection (coherentColimitConstantTriangle B T))
    (coherentColimitTriangleRawLastPrism_projection B T)
    (coherentColimitTriangleRawLast_original_first B T)
    (coherentColimitTriangleRawLastPrism_first B T) g₀ g₁
    (coherentColimitTriangleRawLast_original_terminal B T)
    (coherentColimitTriangleRawLastPrism_terminal B T)

end SerrePositivity.InfinityCategories.F2
