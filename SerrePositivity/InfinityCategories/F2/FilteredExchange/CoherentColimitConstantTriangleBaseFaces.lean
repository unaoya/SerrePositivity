module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantPrismBase
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePrismEdges

/-!
概要：元の定値余極限三角形の三面の全底を、元の三実一次単体へ厳密に戻す。
方針：同じ三角形の面式と元の定値 prism の底表示を合成する。
規約：三辺・全二単体・実始域射を保持。使われ方：最後辺だけを普遍輸送で置き換える。
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
  (p : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
local notation "β" => (Δ[2] ◁ p) ≫ functorSimplexDiagram
  (FunctorCompositionTriangle.diagram (coherentColimitConstantTriangle B T))

/-- 元の定値三角形の最初辺の全底は、元の同じ最初余極限辺の実一次単体。 -/
lemma coherentColimitConstantTriangle_first_base :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ β =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
  exact (functorTrianglePrism_edge_base (coherentColimitConstantTriangle B T).diagram p 2
    _ (coherentColimitConstantTriangle B T).face_two).trans
      (coherentColimitConstantPrism_base B a p)

/-- 元の定値三角形の最後辺の全底は、元の同じ最後余極限辺の実一次単体。 -/
lemma coherentColimitConstantTriangle_last_base :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ β =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B b).edge := by
  exact (functorTrianglePrism_edge_base (coherentColimitConstantTriangle B T).diagram p 0
    _ (coherentColimitConstantTriangle B T).face_zero).trans
      (coherentColimitConstantPrism_base B b p)

/-- 元の定値三角形の長辺の全底は、元の同じ長余極限辺の実一次単体。 -/
lemma coherentColimitConstantTriangle_long_base :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ β =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B d).edge := by
  exact (functorTrianglePrism_edge_base (coherentColimitConstantTriangle B T).diagram p 1
    _ (coherentColimitConstantTriangle B T).face_one).trans
      (coherentColimitConstantPrism_base B d p)

end SerrePositivity.InfinityCategories.F2
