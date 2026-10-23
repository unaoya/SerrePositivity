module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitTriangleRawLastLongData
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedLongWitness

/-!
概要：raw 普遍最終辺を持つ同じ全三角形の長辺の実始点と底を回収する。
方針：共通最初辺の実始点と元の長辺の全底を制限する。
規約：同じ全持ち上げを保持。使われ方：長辺を同じ全区間の輸送族へ拡張する。
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

local notation "H" => (stdSimplex.δ (1 : Fin 3) ▷ E) ≫
  coherentColimitTriangleRawLastPrism B T

local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "q" => fst E (Δ[0] : SSet)
local notation "g" => (ma ≫ coherentColimitRawConstantFiberProjection B G) ≫
  coherentColimitRawFiberTransport B b

/-- 元の最初辺と raw 普遍最終辺の全持ち上げの長辺を、同じ長区間の全輸送にする。 -/
def coherentColimitTriangleRawLastLongTransport :
    FiberTransportFamily
      (b := JoinCocone.vertex (coherentDiagramTotalCocone J)) pointedSpaceProjection
      (coherentColimitRawConstantFiberProjection B F) (intervalMappingUncurry D) where
  endpoint := q ≫ g
  prism := (Δ[1] ◁ q) ≫ H
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coherentColimitTriangleRawLastPrism_long_start]
    rfl
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
    simpa only [coherentColimitRawConstantDiagram, Category.assoc] using congrArg (fun f => q ≫ f)
      (coherentColimitTriangleRawLastPrism_terminal B T)
  over_base := by
    rw [Category.assoc, coherentColimitTriangleRawLastPrism_long_projection,
      coherentColimitRawIntervalVertex_uncurry, ← Category.assoc, whiskerLeft_fst,
      ← Category.assoc, whiskerLeft_fst]

/-- 同じ長区間輸送の一点 prism は、元の全持ち上げの同じ長辺そのもの。 -/
lemma coherentColimitTriangleRawLastLongTransport_point_prism
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 E) (SSet.const v)) ≫
      (coherentColimitTriangleRawLastLongTransport B T).prism = H := by
  change (Δ[1] ◁ lift (𝟙 E) (SSet.const v)) ≫ (Δ[1] ◁ q) ≫ H = H
  rw [← Category.assoc, ← whiskerLeft_comp, lift_fst, whiskerLeft_id, Category.id_comp]

/-- 同じ長区間輸送の一点終点は、元の第一作用後の同じ raw 普遍輸送。 -/
lemma coherentColimitTriangleRawLastLongTransport_point_endpoint
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 E) (SSet.const v) ≫
      (coherentColimitTriangleRawLastLongTransport B T).endpoint = g := by
  change lift (𝟙 E) (SSet.const v) ≫ q ≫ g = g
  rw [← Category.assoc, lift_fst, Category.id_comp]
  rfl

/-- 元の指定長辺輸送の一点 prism も、同じ元の全三角形の長辺そのもの。 -/
lemma coherentColimitConstantTriangleLongTransport_point_prism :
    (Δ[1] ◁ lift (𝟙 E) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
      (coherentColimitConstantTriangleLongTransport B T).prism =
    (stdSimplex.δ (1 : Fin 3) ▷ E) ≫
      functorTrianglePointedLift (coherentColimitConstantTriangle B T) := by
  rw [coherentColimitConstantTriangleLongTransport_prism]
  have hh := functorTrianglePointedLift_long (coherentColimitConstantTriangle B T) (𝟙 E)
  simpa only [coherentColimitRawConstantDiagram, coherentColimitConstantTriangleLongWitness,
    whiskerLeft_id, Category.id_comp,
    prismParameterRestriction, UnstraighteningFamilyWitness.leftPrism, Category.assoc] using hh.symm

end SerrePositivity.InfinityCategories.F2
