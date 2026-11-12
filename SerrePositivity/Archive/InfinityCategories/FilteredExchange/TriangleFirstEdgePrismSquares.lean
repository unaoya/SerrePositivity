module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleFirstEdgeLeftAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：最初の辺を固定した全三角形の長辺と最後辺の実初期値・実終点の可換正方形。
方針：元の二単体の各頂点を全係数で計算する。
規約：全係数と実面写像を保持。使われ方：同じ全比較の二辺への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 長辺の始点は、固定した最初の辺の元の始点そのもの。 -/
lemma triangleFirstEdge_long_initial_square (A : SSet.{u}) :
    prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 最後辺の始点は、固定した最初の辺の元の終点そのもの。 -/
lemma triangleFirstEdge_last_initial_square (A : SSet.{u}) :
    prismEndpoint 0 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 最後辺と長辺の実終点は、同じ全係数上で厳密に一致する。 -/
lemma triangleFirstEdge_last_final_square (A : SSet.{u}) :
    prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) =
      prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
