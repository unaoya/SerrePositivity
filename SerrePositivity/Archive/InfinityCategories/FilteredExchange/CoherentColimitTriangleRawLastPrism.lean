module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitTriangleRawLastLift

/-!
概要：同じ元の全三角形と最初辺を保つ raw 普遍最終辺の持ち上げを保持する。
方針：元の存在証明から全持ち上げを選び、三面条件と実終点をそのまま回収する。
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

/-- 元の最初辺を保ち、最後辺を同じ raw 普遍輸送にした全三角形の持ち上げ。 -/
def coherentColimitTriangleRawLastPrism :
    (Δ[2] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u} :=
  Classical.choose (exists_coherentColimitTriangleRawLastLift B T)

/-- 選んだ全持ち上げの最初辺は、元の同じ最初辺の実 prism。 -/
lemma coherentColimitTriangleRawLastPrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ coherentColimitTriangleRawLastPrism B T = H₀₁ :=
  (Classical.choose_spec (exists_coherentColimitTriangleRawLastLift B T)).1

/-- 選んだ全持ち上げの最後辺は、同じ指定点・同じ初期値の raw 普遍輸送。 -/
lemma coherentColimitTriangleRawLastPrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ E) ≫ coherentColimitTriangleRawLastPrism B T = H₁₂ :=
  (Classical.choose_spec (exists_coherentColimitTriangleRawLastLift B T)).2.1

/-- 選んだ全持ち上げの底は、同じ元の全二単体そのもの。 -/
lemma coherentColimitTriangleRawLastPrism_projection :
    coherentColimitTriangleRawLastPrism B T ≫ pointedSpaceProjection = β :=
  (Classical.choose_spec (exists_coherentColimitTriangleRawLastLift B T)).2.2

/-- 同じ全持ち上げの長辺の実終点は、元の第一作用後の同じ raw 普遍輸送の終点。 -/
lemma coherentColimitTriangleRawLastPrism_terminal :
    (prismEndpoint 1 E ≫ (stdSimplex.δ (1 : Fin 3) ▷ E)) ≫
      coherentColimitTriangleRawLastPrism B T =
    ((ma ≫ coherentColimitRawConstantFiberProjection B G) ≫
      coherentColimitRawFiberTransport B b) ≫
        vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [← triangleRightPrism_terminal, Category.assoc,
    coherentColimitTriangleRawLastPrism_last, coherentColimitRawTransportPointPrism_finish]

end SerrePositivity.InfinityCategories.F2
