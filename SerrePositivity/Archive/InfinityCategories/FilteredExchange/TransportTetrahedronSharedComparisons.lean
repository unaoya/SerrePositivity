module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTetrahedronSharedEdges
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleParallelComparisons

/-!
概要：四面体の六本の実共有辺では、元の選択済み比較も同じ値になる。
方針：同じ実 prism の厳密等式から、底の族と指定比較の HEq を回収する。
規約：端点の同値だけへ弱めない。使われ方：四面の貼り合わせの中間因子消去。
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

/-- 元の実辺 01 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison01 :
    HEq (D.face 2).diagram.bottomComparison (D.face 3).diagram.bottomComparison := by
  exact transportTriangle_bottomComparison_shared_heq
    (D.face 2) (D.face 3) D.shared_edge01

/-- 元の実辺 02 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison02 :
    HEq (D.face 1).diagram.bottomComparison (D.face 3).diagram.leftComparison := by
  unfold TransportSquareDiagram.bottomComparison TransportSquareDiagram.leftComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ D.shared_edge02

/-- 元の実辺 03 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison03 :
    HEq (D.face 1).diagram.leftComparison (D.face 2).diagram.leftComparison := by
  exact transportTriangle_leftComparison_shared_heq
    (D.face 1) (D.face 2) D.shared_edge03

/-- 元の実辺 12 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison12 :
    HEq (D.face 0).diagram.bottomComparison (D.face 3).diagram.rightComparison := by
  unfold TransportSquareDiagram.bottomComparison TransportSquareDiagram.rightComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ D.shared_edge12

/-- 元の実辺 13 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison13 :
    HEq (D.face 0).diagram.leftComparison (D.face 2).diagram.rightComparison := by
  unfold TransportSquareDiagram.leftComparison TransportSquareDiagram.rightComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ D.shared_edge13

/-- 元の実辺 23 の指定比較は、両面で同じ値。 -/
lemma TransportTetrahedronDiagram.shared_comparison23 :
    HEq (D.face 0).diagram.rightComparison (D.face 1).diagram.rightComparison := by
  exact transportTriangle_rightComparison_shared_heq
    (D.face 0) (D.face 1) D.shared_edge23

end SerrePositivity.InfinityCategories.F2
