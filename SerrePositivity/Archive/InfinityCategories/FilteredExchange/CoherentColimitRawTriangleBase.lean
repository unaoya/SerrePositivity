module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleBaseFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorConstantSimplexBase

/-!
概要：元の定値余極限全三角形の底を、元の余極限関手の同じ実二単体へ戻す。
方針：任意の全係数上で定値図式の底の一般式を適用する。
規約：元の全二単体と実係数射を保持。使われ方：普遍二辺の三角形を元の底へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値三角形の底は、元の指定二単体の余極限関手による全像そのもの。 -/
lemma coherentColimitConstantTriangle_base (B : SSet.{u})
    {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
    (p : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B) :
    (Δ[2] ◁ p) ≫ functorSimplexDiagram (coherentColimitConstantTriangle B T).diagram =
      fst (Δ[2] : SSet.{u + 1}) K ≫ T.diagram ≫ coherentColimitFunctor B := by
  change (Δ[2] ◁ p) ≫ functorSimplexDiagram
    (T.diagram ≫ coherentColimitFunctor B ≫ constantDiagram _ SpaceInfinity) = _
  simpa only [Category.assoc] using
    functorSimplexDiagram_constant_base p (T.diagram ≫ coherentColimitFunctor B)

/-- 元の指定余極限辺の実一次単体は、元の同じ Homotopy の余極限関手による像。 -/
lemma coherentColimitFunctorEdge_simplex (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : SSet.Homotopy F G) :
    SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge =
      MonoidalClosed.curry a.h ≫ coherentColimitFunctor B := by
  change SSet.yonedaEquiv.symm ((coherentColimitFunctor B).app _
    (functorEdgeOfSimplicialHomotopy a).edge) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.F2
