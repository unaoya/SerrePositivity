module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePointedEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismBase

/-!
概要：元の全三角形の各辺の底と、右辺の二端を同じ全係数の prism 表示へ揃える。
方針：元の面式と全底上の展開の自然性を使い、共有頂点を厳密に比較する。
規約：任意の全係数と指定された円柱を保持。使われ方：元の右辺比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定三角形の辺の全底は、元の同じ指定変換の全 prism の底。 -/
lemma functorTrianglePrism_edge_base {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
    (P : (Δ[2] : SSet.{u + 1}) ⟶ (ihom B).obj SpaceInfinity.{u})
    (p : C ⟶ B) (i : Fin 3) (H : SSet.Homotopy F G)
    (h : stdSimplex.δ i ≫ P = curry H.h) :
    (stdSimplex.δ i ▷ C) ≫ (Δ[2] ◁ p) ≫ functorSimplexDiagram P =
      (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h) := by
  have hn : (stdSimplex.δ i ▷ C) ≫ (Δ[2] ◁ p) =
      (Δ[1] ◁ p) ≫ (stdSimplex.δ i ▷ B) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hn, Category.assoc, functorSimplexDiagram_pre, h]

/-- 元の右辺の始点は、同じ全三角形の第一辺の終点そのもの。 -/
lemma triangleRightPrism_initial (C : SSet.{u}) :
    prismEndpoint 0 C ≫ (stdSimplex.δ (0 : Fin 3) ▷ C) =
      prismEndpoint 1 C ≫ (stdSimplex.δ (2 : Fin 3) ▷ C) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の右辺と長辺の終点は、同じ全三角形の最終頂点そのもの。 -/
lemma triangleRightPrism_terminal (C : SSet.{u}) :
    prismEndpoint 1 C ≫ (stdSimplex.δ (0 : Fin 3) ▷ C) =
      prismEndpoint 1 C ≫ (stdSimplex.δ (1 : Fin 3) ▷ C) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の全三角形の中間頂点は、同じ元の中間図式を被覆する。 -/
lemma functorTrianglePrism_middle_base {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) :
    simplexPrismVertex 2 1 C ≫ (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram = p ≫ G := by
  have hv : simplexPrismVertex 2 1 C =
      prismEndpoint 1 C ≫ (stdSimplex.δ (2 : Fin 3) ▷ C) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hv, Category.assoc, functorTrianglePrism_edge_base T.diagram p 2 a T.face_two]
  exact functorHomotopyPrismBase_target a p

/-- 元の全三角形の最終頂点は、同じ元の標的図式を被覆する。 -/
lemma functorTrianglePrism_terminal_base {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) :
    simplexPrismVertex 2 2 C ≫ (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram = p ≫ J := by
  have hv : simplexPrismVertex 2 2 C =
      prismEndpoint 1 C ≫ (stdSimplex.δ (1 : Fin 3) ▷ C) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hv, Category.assoc, functorTrianglePrism_edge_base T.diagram p 1 c T.face_one]
  exact functorHomotopyPrismBase_target c p

end SerrePositivity.InfinityCategories.F2
