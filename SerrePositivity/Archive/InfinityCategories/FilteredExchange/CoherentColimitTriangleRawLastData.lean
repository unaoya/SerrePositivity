module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitTriangleRawLastPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleFirstEdgeFiberRestrictionEquality

/-!
概要：元の全三角形と raw 最終辺の全持ち上げの共通最初辺・底・終点を揃える。
方針：元の二つの指定作用と全三角形の実辺の端点式を使う。
規約：比較対象は同じ指定二単体上に置く。使われ方：長辺比較と最後辺比較の同時制限。
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

/-- 元の指定三角形の最初辺は、置換後と同じ元の実 prism。 -/
lemma coherentColimitTriangleRawLast_original_first :
    (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ W₀ = H₀₁ := by
  simpa only [coherentColimitRawConstantDiagram,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] using
    functorTrianglePointedLift_first (coherentColimitConstantTriangle B T) (𝟙 E)

/-- 元の指定三角形の長辺の実終点は、元の同じ二つの作用後の fiber 座標。 -/
lemma coherentColimitTriangleRawLast_original_terminal :
    j ≫ W₀ = (ma ≫ mb ≫ coherentColimitRawConstantFiberProjection B J) ≫
      vertexFiberι pointedSpaceProjection z := by
  dsimp only [coherentColimitRawConstantDiagram]
  have hs := functorTrianglePointedLift_second (coherentColimitConstantTriangle B T) (𝟙 E)
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp] at hs
  rw [← triangleRightPrism_terminal, Category.assoc, hs,
    functorHomotopyPointedPrism_target]
  simp only [Category.assoc, coherentColimitRawConstantFiberProjection,
    constantUnstraighteningFiberProjection_ι]

/-- 同じ全三角形の最終頂点は、元の同じ余錐頂点で厳密に一定。 -/
lemma coherentColimitTriangleRawLast_terminal_base :
    j ≫ β = SSet.const z := by
  change simplexPrismVertex 2 2 E ≫
    (Δ[2] ◁ leftUnstraighteningProjection (coherentColimitRawConstantDiagram B F)) ≫
      functorSimplexDiagram (coherentColimitConstantTriangle B T).diagram = _
  rw [functorTrianglePrism_terminal_base, SSet.comp_const]

/-- 共通最初辺の底は、元の同じ全三角形の第一辺そのもの。 -/
lemma coherentColimitTriangleRawLast_first_base :
    H₀₁ ≫ pointedSpaceProjection = (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ β := by
  rw [← coherentColimitTriangleRawLast_original_first B T, Category.assoc,
    functorTrianglePointedLift_projection]

end SerrePositivity.InfinityCategories.F2
