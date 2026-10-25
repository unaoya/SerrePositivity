module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleParameter

/-!
概要：元の二単体への折り畳みは、同じ実三頂点を全係数で保持する。
方針：下辺の厳密な等式と、最終頂点での実成分を計算する。
規約：係数を変更しない。使われ方：実二単体から三角形持ち上げを作る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 畳み込みの下二隅は、元の二単体の第一辺の同じ二端点である。 -/
lemma transportTriangleParameter_bottom_corner (P : SSet.{u}) (i : Fin 2) :
    (prismEndpoint i P ≫ prismEndpoint 0 _) ≫ transportTriangleParameter P =
      prismEndpoint i P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) := by
  rw [Category.assoc, transportTriangleParameter_bottom]

/-- 畳み込みの左上隅は、元の二単体の長辺の同じ終点である。 -/
lemma transportTriangleParameter_last_corner (P : SSet.{u}) :
    (prismEndpoint 0 P ≫ prismEndpoint 1 _) ≫ transportTriangleParameter P =
      prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
