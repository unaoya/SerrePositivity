module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawFirstChoiceTriangleEvaluation

/-!
概要：元の二単体と指定二実辺を持つ任意の全三角形の長辺の実データを回収する。
方針：元の二辺の等式を実頂点と底へ制限する。
規約：全持ち上げを選び直さない。使われ方：全比較の元の長辺残余への同定。
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
  (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (g : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone G)))
  (Y : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hY : Y ≫ pointedSpaceProjection = fst (Δ[2] : SSet.{u + 1}) K ≫
    T.diagram ≫ coherentColimitFunctor B)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ Y = W)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ Y = coherentColimitRawTransportPointPrism B b g)

include hY in
/-- 元の任意の二辺固定三角形の長辺は、同じ元の指定長辺を厳密に被覆する。 -/
lemma coherentColimitRawTriangleLong_projection :
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Y) ≫ pointedSpaceProjection =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B d).edge := by
  rw [Category.assoc, hY]
  exact coherentColimitRawTriangle_face B d T.diagram 1 T.face_one

include hs hfirst in
/-- 元の任意の二辺固定三角形の長辺は、同じ元の第一辺の実始点を持つ。 -/
lemma coherentColimitRawTriangleLong_start :
    prismEndpoint 0 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Y =
      f ≫ vertexFiberι pointedSpaceProjection
        (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [← Category.assoc, triangleFirstEdge_long_initial_square, Category.assoc, hfirst, hs]

include hlast in
/-- 元の任意の二辺固定三角形の長辺終点は、同じ第一辺終点への最後辺普遍輸送。 -/
lemma coherentColimitRawTriangleLong_finish :
    prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Y =
      (g ≫ coherentColimitRawFiberTransport B b) ≫ vertexFiberι pointedSpaceProjection
        (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [← Category.assoc, ← triangleFirstEdge_last_final_square, Category.assoc, hlast,
    coherentColimitRawTransportPointPrism_finish]

include f in
/-- 元の全二単体の最終実頂点の底は、元の同じ最終余錐頂点に厳密に一定。 -/
lemma coherentColimitRawTriangle_terminal_base :
    (prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
      (fst (Δ[2] : SSet.{u + 1}) K ≫ T.diagram ≫ coherentColimitFunctor B) =
        SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone J)) := by
  rw [Category.assoc, coherentColimitRawTriangle_face B d T.diagram 1 T.face_one]
  exact coherentColimitRawFirstChoice_final_base B d f

end SerrePositivity.InfinityCategories.F2
