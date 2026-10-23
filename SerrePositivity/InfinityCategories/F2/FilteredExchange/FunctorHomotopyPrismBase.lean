module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPointedPrism

/-!
概要：元の指定変換の全 prism の底の両端を、元の二図式へ厳密に同定する。
方針：全底上の展開と元の円柱の両端の式を使う。
規約：始点の実射の存在を仮定しない。使われ方：始点も動く全 prism 空間の評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B)

/-- 元の全 prism の底の始点は、同じ元の始域図式。 -/
lemma functorHomotopyPrismBase_source :
    prismEndpoint 0 C ≫ (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h) = p ≫ F := by
  have h : prismEndpoint 0 B ≫ functorSimplexDiagram (curry H.h) = F := by
    rw [functorSimplexDiagram, uncurry_curry]
    change SSet.ι₀ ≫ H.h = F
    exact H.h₀
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h]

/-- 元の全 prism の底の終点は、同じ元の標的図式。 -/
lemma functorHomotopyPrismBase_target :
    prismEndpoint 1 C ≫ (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h) = p ≫ G := by
  have h : prismEndpoint 1 B ≫ functorSimplexDiagram (curry H.h) = G := by
    rw [functorSimplexDiagram, uncurry_curry]
    change SSet.ι₁ ≫ H.h = G
    exact H.h₁
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h]

end SerrePositivity.InfinityCategories.F2
