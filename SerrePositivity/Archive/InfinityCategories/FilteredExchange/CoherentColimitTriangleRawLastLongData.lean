module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitTriangleRawLastPointComparison

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

/-- 同じ長辺の実始点は、元の raw fiber 射影の pointed 包含そのもの。 -/
lemma coherentColimitTriangleRawLastPrism_long_start :
    prismEndpoint 0 E ≫ H = coherentColimitRawConstantFiberProjection B F ≫
      vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
    coherentColimitTriangleRawLastPrism_first, functorHomotopyPointedPrism_source,
    Category.id_comp]
  exact (constantUnstraighteningFiberProjection_ι _ _).symm

/-- 同じ長辺の全底は、元の同じ長余極限辺の実一次単体。 -/
lemma coherentColimitTriangleRawLastPrism_long_projection :
    H ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) E ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B d).edge := by
  rw [Category.assoc, coherentColimitTriangleRawLastPrism_projection]
  exact coherentColimitConstantTriangle_long_base B T _

end SerrePositivity.InfinityCategories.F2
