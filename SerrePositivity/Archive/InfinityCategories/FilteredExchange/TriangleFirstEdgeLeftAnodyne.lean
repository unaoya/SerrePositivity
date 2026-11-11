module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：最初の辺を固定した全三角形の延長空間を扱うための left anodyne な包含。
方針：最初の頂点を保つ join の単射を標準二単体の最初の辺へ移す。
規約：元の全係数を保持。使われ方：長辺比較と最後辺比較を同じ全持ち上げで照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最初の辺の包含は left anodyne であり、元の辺全体を初期値として固定できる。 -/
lemma triangleFirstEdge_leftAnodyne :
    leftAnodyneExtensions (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  have h := (leftAnodyneExtensions.cancel_right_of_respectsIso
    (joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2)))
    (joinStdSimplexIso 0 1).hom).mpr
      (joinPoint_mono_leftAnodyne (stdSimplex.δ (1 : Fin 2)))
  rw [joinStdSimplexIso_vertex_one] at h
  exact (leftAnodyneExtensions.cancel_left_of_respectsIso
    (joinStdSimplexIso 0 0).hom (stdSimplex.δ (2 : Fin 3))).mp h

/-- 任意の元の全係数を保っても、最初の辺の固定は left anodyne な包含である。 -/
lemma triangleFirstEdge_prism_leftAnodyne (A : SSet.{u}) :
    leftAnodyneExtensions (stdSimplex.δ (2 : Fin 3) ▷ A) :=
  leftAnodyneExtensions_whiskerRight _ triangleFirstEdge_leftAnodyne A

end SerrePositivity.InfinityCategories.F2
