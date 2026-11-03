module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTetrahedronSelectedFaces

/-!
概要：共通六辺上の四面の元の指定合成比較を、同じ実三辺で計算する。
方針：共有辺の元の比較の HEq を、実三角形の貼り合わせ式へ代入する。
規約：四面体整合を仮定しない。使われ方：四面の中間因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 面 012 の元の比較を、共通の実三辺の元の比較で貼り合わせる。 -/
lemma TransportTetrahedronDiagram.comparison012_eq :
    D.comparison012 (f 0) =
      (D.edgeComparison12 ≪≫
        diagonalFiberTransport_sourceIso p D.edgeComparison01 D.edge12).symm ≪≫
          D.edgeComparison02 := by
  exact (D.face 3).comparisonAlong_eq D.edge01 D.edge12 D.edge02
    rfl rfl rfl
    D.edgeComparison01 D.edgeComparison12 D.edgeComparison02
    HEq.rfl HEq.rfl HEq.rfl

/-- 面 013 の元の比較を、共通の実三辺の元の比較で貼り合わせる。 -/
lemma TransportTetrahedronDiagram.comparison013_eq :
    D.comparison013 (f 0) =
      (D.edgeComparison13 ≪≫
        diagonalFiberTransport_sourceIso p D.edgeComparison01 D.edge13).symm ≪≫
          D.edgeComparison03 := by
  exact (D.face 2).comparisonAlong_eq D.edge01 D.edge13 D.edge03
    D.shared_curve01 rfl D.shared_curve03.symm
    D.edgeComparison01 D.edgeComparison13 D.edgeComparison03
    D.shared_comparison01 HEq.rfl D.shared_comparison03.symm

/-- 面 023 の元の比較を、共通の実三辺の元の比較で貼り合わせる。 -/
lemma TransportTetrahedronDiagram.comparison023_eq :
    D.comparison023 (f 0) =
      (D.edgeComparison23 ≪≫
        diagonalFiberTransport_sourceIso p D.edgeComparison02 D.edge23).symm ≪≫
          D.edgeComparison03 := by
  exact (D.face 1).comparisonAlong_eq D.edge02 D.edge23 D.edge03
    D.shared_curve02 rfl rfl
    D.edgeComparison02 D.edgeComparison23 D.edgeComparison03
    D.shared_comparison02 HEq.rfl HEq.rfl

/-- 面 123 の元の比較を、共通の実三辺の元の比較で貼り合わせる。 -/
lemma TransportTetrahedronDiagram.comparison123_eq :
    D.comparison123 (f 1) =
      (D.edgeComparison23 ≪≫
        diagonalFiberTransport_sourceIso p D.edgeComparison12 D.edge23).symm ≪≫
          D.edgeComparison13 := by
  exact (D.face 0).comparisonAlong_eq D.edge12 D.edge23 D.edge13
    D.shared_curve12 D.shared_curve23 D.shared_curve13
    D.edgeComparison12 D.edgeComparison23 D.edgeComparison13
    D.shared_comparison12 D.shared_comparison23 D.shared_comparison13

end SerrePositivity.InfinityCategories.F2
