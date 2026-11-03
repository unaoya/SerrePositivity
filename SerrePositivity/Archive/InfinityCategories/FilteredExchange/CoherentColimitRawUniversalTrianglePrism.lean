module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTriangleLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleFirstEdgePrismSquares

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
local notation "H₀₁" => coherentColimitRawTransportPointPrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (f ≫ coherentColimitRawFiberTransport B a)
local notation "β" => fst Δ[2] K ≫ FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

/-- 元の全二単体上の二つの raw 普遍辺を持つ全持ち上げを保持する。 -/
def coherentColimitRawUniversalTrianglePrism :
    (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u} :=
  Classical.choose (exists_coherentColimitRawUniversalTriangleLift B T f)

/-- 同じ全持ち上げの第一辺は、同じ元の raw 第一普遍輸送。 -/
lemma coherentColimitRawUniversalTrianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ coherentColimitRawUniversalTrianglePrism B T f = H₀₁ :=
  (Classical.choose_spec (exists_coherentColimitRawUniversalTriangleLift B T f)).1

/-- 同じ全持ち上げの最後辺は、元の第一普遍輸送後の同じ元の raw 最後辺輸送。 -/
lemma coherentColimitRawUniversalTrianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ coherentColimitRawUniversalTrianglePrism B T f = H₁₂ :=
  (Classical.choose_spec (exists_coherentColimitRawUniversalTriangleLift B T f)).2.1

/-- 同じ全持ち上げは元の全二単体の余極限関手による像を厳密に被覆する。 -/
lemma coherentColimitRawUniversalTrianglePrism_projection :
    coherentColimitRawUniversalTrianglePrism B T f ≫ pointedSpaceProjection = β :=
  (Classical.choose_spec (exists_coherentColimitRawUniversalTriangleLift B T f)).2.2

/-- 同じ普遍三角形の長辺の始点は、元の全初期値そのもの。 -/
lemma coherentColimitRawUniversalTrianglePrism_long_start :
    prismEndpoint 0 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫
      coherentColimitRawUniversalTrianglePrism B T f =
        f ≫ vertexFiberι pointedSpaceProjection
          (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc,
    coherentColimitRawUniversalTrianglePrism_first, coherentColimitRawTransportPointPrism_start]

/-- 同じ普遍三角形の長辺の終点は、元の同じ二つの raw 普遍輸送の実合成射。 -/
lemma coherentColimitRawUniversalTrianglePrism_long_finish :
    prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫
      coherentColimitRawUniversalTrianglePrism B T f =
    ((f ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b) ≫
      vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [← Category.assoc, ← triangleFirstEdge_last_final_square, Category.assoc,
    coherentColimitRawUniversalTrianglePrism_last, coherentColimitRawTransportPointPrism_finish]

end SerrePositivity.InfinityCategories.F2
