module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceTriangleEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawConstantEdgePointPrism

/-!
概要：全第一辺の三角形族を元の実第一辺で評価し、同じ指定二単体と二実辺を回収する。
方針：元の実頂点での普遍 prism 評価と最後辺普遍輸送の自然性を使う。
規約：元の実第一辺と指定二単体を保持。使われ方：全長辺比較の二成分の同定。
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
  (W : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
    SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
  (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "q" => coherentColimitRawFirstChoiceVertex B a f W hp hs
local notation "r" => lift (𝟙 K) (SSet.const q)

local notation "X" => coherentColimitRawFirstChoiceTriangleAtVertex B T f W hp hs

/-- 元の第一辺での全三角形の長辺は、同じ元の全初期値を保つ。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_long_start :
    prismEndpoint 0 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X =
      f ≫ vertexFiberι pointedSpaceProjection
        (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
    coherentColimitRawFirstChoiceTriangleAtVertex_first B T f W hp hs, hs]

/-- 元の第一辺での全三角形の長辺は、元の同じ指定長辺の実底を持つ。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_long_projection :
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X) ≫ pointedSpaceProjection =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B d).edge := by
  rw [Category.assoc, coherentColimitRawFirstChoiceTriangleAtVertex_projection B T f W hp hs]
  exact coherentColimitRawTriangle_face B d T.diagram 1 T.face_one

/-- 元の第一辺での全三角形の長辺の実終点は、同じ元の第一辺終点後の最後辺普遍輸送。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_long_finish
    (g : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hg : prismEndpoint 1 K ≫ W = g ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G))) :
    prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X =
    (g ≫ coherentColimitRawFiberTransport B b) ≫
      vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [← Category.assoc, ← triangleFirstEdge_last_final_square, Category.assoc,
    coherentColimitRawFirstChoiceTriangleAtVertex_last B T f W hp hs g hg,
    coherentColimitRawTransportPointPrism_finish]

/-- 同じ全長辺輸送の元の実頂点での制限は、評価した全三角形の同じ長辺そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleAtVertex_long_point_prism :
    (Δ[1] ◁ r) ≫ (coherentColimitRawFirstChoiceTriangleLongTransport B T f).prism =
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ X :=
  (trianglePrism_restrict_baseChange r (coherentColimitRawFirstChoiceTrianglePrism B T f) 1).symm

end SerrePositivity.InfinityCategories.F2
