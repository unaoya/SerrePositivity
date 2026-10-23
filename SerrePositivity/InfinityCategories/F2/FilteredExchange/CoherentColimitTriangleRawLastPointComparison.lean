module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitTriangleRawLastRestricted
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTransportPointPrecomp

/-!
概要：元の全三角形の長辺比較を、元の最後辺の指定一点輸送比較へ値まで同定する。
方針：同じ全持ち上げの最後辺制限と、元の一点比較の前合成式を合成する。
規約：元の全二単体・元の作用・指定比較を保持。使われ方：長辺残余の因子消去。
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

local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "w" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (Functor.obj SSet.uliftFunctor B) A)
local notation "U" => pointedIntervalTransportSource P A
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift ma (SSet.const l)

/-- 元の長辺と raw 普遍最終辺の比較は、元の最後辺の指定一点比較の同じ前合成。 -/
lemma coherentColimitTriangleRawLastLongComparison_heq_point :
    HEq (coherentColimitTriangleRawLastLongComparison B T)
      ((coherentColimitConstantTransportPointIso B b).precomp ma) := by
  have hr := coherentColimitTriangleRawLastLongComparison_heq_restricted B T
  have he := fiberTransportRestrictedPrismComparison_eq_endpointIso pointedSpaceProjection P
    (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s
  have hs := congrArg (fun e => e.precomp s)
    (pointedIntervalTransportComparison_eq_source P A w)
  exact hr.trans ((heq_of_eq he).trans ((heq_of_eq hs).symm.trans
    (coherentColimitConstantTransportPointIso_precomp_heq B b ma).symm))

end SerrePositivity.InfinityCategories.F2
