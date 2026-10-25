module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronFacePasting
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleAlongNaturality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoInverse
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TetrahedronIsoCancellation

/-!
概要：同じ実四面体の元の四つの指定輸送比較は、四面体の合成則を満たす。
方針：実共有辺の比較を四面の貼り合わせ式へ代入し、元の始点自然性で消去する。
規約：高次整合を仮定で追加しない。使われ方：元の二段評価の指定合成比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実四面体の四面から回収した元の指定合成比較の四面体則。 -/
lemma TransportTetrahedronDiagram.comparison_coherence
    {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {v : Fin 4 → B _⦋0⦌}
    {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f) :
    diagonalFiberTransport_sourceIso p (D.comparison012 (f 0)) D.edge23 ≪≫
        D.comparison023 (f 0) =
      D.comparison123 (diagonalFiberTransport p (f 0) D.edge01) ≪≫
        D.comparison013 (f 0) := by
  refine tetrahedronIsoCancellation
    (diagonalFiberTransport_sourceIso p
      (diagonalFiberTransport_sourceIso p D.edgeComparison01 D.edge12) D.edge23)
    (diagonalFiberTransport_sourceIso p D.edgeComparison12 D.edge23)
    D.edgeComparison23
    (diagonalFiberTransport_sourceIso p D.edgeComparison02 D.edge23)
    D.edgeComparison13
    (diagonalFiberTransport_sourceIso p D.edgeComparison01 D.edge13)
    D.edgeComparison03 _ _ (D.comparison123 (f 1)) _ _ ?_ ?_ ?_ ?_ ?_
  · rw [D.comparison012_eq]
    simp only [← diagonalFiberTransport_sourceIso_trans, diagonalFiberTransport_sourceIso_symm]
  · exact D.comparison023_eq
  · exact D.comparison123_eq
  · exact D.comparison013_eq
  · exact (D.face 0).comparisonAlong_source_naturality D.edge12 D.edge23 D.edge13
      D.shared_curve12 D.shared_curve23 D.shared_curve13 D.edgeComparison01

end SerrePositivity.InfinityCategories.F2
