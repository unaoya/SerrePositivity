module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstChoiceTriangleLift
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleFirstEdgePrismSquares

/-!
概要：元の余極限二単体上で、元の二つの raw 普遍輸送を辺に持つ全三角形を充填する。
方針：同じ普遍 prism の実中間点と元の二面式を使う。
規約：全係数・初期値・元の全二単体を保持。使われ方：新長辺残余の普遍三角形への照合。
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
local notation "Q" => coherentColimitRawFirstChoiceSpace B a f
local notation "H₀₁" => coherentColimitRawFirstChoicePrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (coherentColimitRawFirstChoiceEndpoint B a f)
local notation "β" => fst Δ[2] (K ⊗ Q) ≫
  FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

/-- 元の全第一辺選択に沿う、同じ指定二単体と最後辺普遍輸送を持つ全三角形。 -/
def coherentColimitRawFirstChoiceTrianglePrism :
    (Δ[2] : SSet.{u + 1}) ⊗ (K ⊗ Q) ⟶ PointedSpaceInfinity.{u} :=
  Classical.choose (exists_coherentColimitRawFirstChoiceTriangleLift B T f)

/-- 全三角形の第一辺は、元の全第一辺選択空間の同じ全評価 prism。 -/
lemma coherentColimitRawFirstChoiceTrianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Q)) ≫
      coherentColimitRawFirstChoiceTrianglePrism B T f = H₀₁ :=
  (Classical.choose_spec (exists_coherentColimitRawFirstChoiceTriangleLift B T f)).1

/-- 全三角形の最後辺は、元の全第一辺の終点への同じ元の raw 普遍輸送。 -/
lemma coherentColimitRawFirstChoiceTrianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Q)) ≫
      coherentColimitRawFirstChoiceTrianglePrism B T f = H₁₂ :=
  (Classical.choose_spec (exists_coherentColimitRawFirstChoiceTriangleLift B T f)).2.1

/-- 全第一辺選択の上で、元の指定二単体の全像を厳密に被覆する。 -/
lemma coherentColimitRawFirstChoiceTrianglePrism_projection :
    coherentColimitRawFirstChoiceTrianglePrism B T f ≫ pointedSpaceProjection = β :=
  (Classical.choose_spec (exists_coherentColimitRawFirstChoiceTriangleLift B T f)).2.2

/-- 全三角形の長辺の実始点は、元の同じ全初期値の選択空間への引き戻し。 -/
lemma coherentColimitRawFirstChoiceTrianglePrism_long_start :
    prismEndpoint 0 (K ⊗ Q) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Q)) ≫
      coherentColimitRawFirstChoiceTrianglePrism B T f =
    fst K Q ≫ f ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
    coherentColimitRawFirstChoiceTrianglePrism_first, coherentColimitRawFirstChoicePrism_start]

/-- 全長辺の実終点は、同じ全第一辺の fiber 終点に最後辺輸送を後合成したものそのもの。 -/
lemma coherentColimitRawFirstChoiceTrianglePrism_long_finish :
    prismEndpoint 1 (K ⊗ Q) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ Q)) ≫
      coherentColimitRawFirstChoiceTrianglePrism B T f =
    (coherentColimitRawFirstChoiceEndpoint B a f ≫ coherentColimitRawFiberTransport B b) ≫
      vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [← Category.assoc, ← triangleFirstEdge_last_final_square, Category.assoc,
    coherentColimitRawFirstChoiceTrianglePrism_last, coherentColimitRawTransportPointPrism_finish]

end SerrePositivity.InfinityCategories.F2
