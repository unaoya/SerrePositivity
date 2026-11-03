module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismBase
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorConstantPrismBase

/-!
概要：元の定値余極限辺の全 prism の底を、元の実一次単体の同じ全係数表示へ戻す。
方針：元の定値辺の curry 表示と、直積の二射影の厳密な自然性を使う。
規約：元の円柱と実底射を保持。使われ方：普遍 fiber 輸送の prism と同じ底で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値余極限辺の底は、元の同じ一次単体を全係数で引き戻したものそのもの。 -/
lemma coherentColimitConstantPrism_base (B : SSet.{u})
    {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (b : SSet.Homotopy G J) {K : SSet.{u + 1}}
    (p : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B) :
    (Δ[1] ◁ p) ≫ functorSimplexDiagram
      (curry (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)).h) =
    fst (Δ[1] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B b).edge := by
  change (Δ[1] ◁ p) ≫ functorSimplexDiagram
    (curry (uncurry (SSet.yonedaEquiv.symm (coherentColimitConstantEdge B b).edge))) = _
  exact functorSimplexDiagram_constant_base_of_eq p
    (SSet.yonedaEquiv.symm (coherentColimitConstantEdge B b).edge)
    (SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B b).edge)
    (coherentColimitConstantEdge_curry B b)

end SerrePositivity.InfinityCategories.F2
