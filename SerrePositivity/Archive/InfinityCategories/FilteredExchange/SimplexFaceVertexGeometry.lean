module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：標準単体の実面と実頂点の制限は、元の頂点番号を厳密に保持する。
方針：標準単体の各成分で同じ単調写像を計算する。
規約：全係数を保持。使われ方：同じ実四面体から全三角形面を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 面の元の頂点は、同じ全係数上で省略番号を補った元の頂点になる。 -/
lemma simplexPrismVertex_face {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) (P : SSet.{u}) :
    simplexPrismVertex n i P ≫ (stdSimplex.δ k ▷ P) =
      simplexPrismVertex (n + 1) (k.succAbove i) P := by
  apply SSet.hom_ext
  intro d
  rfl

/-- 元の三角形の第一辺の始点は、同じ零番頂点。 -/
lemma trianglePrism_initial_vertex (P : SSet.{u}) :
    prismEndpoint 0 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) = simplexPrismVertex 2 0 P := by
  apply SSet.hom_ext
  intro d
  rfl

/-- 元の三角形の第一辺の終点は、同じ一番頂点。 -/
lemma trianglePrism_middle_vertex (P : SSet.{u}) :
    prismEndpoint 1 P ≫ (stdSimplex.δ (2 : Fin 3) ▷ P) = simplexPrismVertex 2 1 P := by
  apply SSet.hom_ext
  intro d
  rfl

/-- 元の三角形の長辺の終点は、同じ二番頂点。 -/
lemma trianglePrism_final_vertex (P : SSet.{u}) :
    prismEndpoint 1 P ≫ (stdSimplex.δ (1 : Fin 3) ▷ P) = simplexPrismVertex 2 2 P := by
  apply SSet.hom_ext
  intro d
  rfl

end SerrePositivity.InfinityCategories.F2
