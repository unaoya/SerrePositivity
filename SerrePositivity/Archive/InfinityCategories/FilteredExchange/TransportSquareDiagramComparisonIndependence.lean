module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramBottomNaturality
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramLeftNaturality
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramRightNaturality
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramTopNaturality

/-!
概要：左下角だけを固定した任意の実四角形の、四辺による指定比較値は同じ。
方針：左右の二辺の合成へ全延長比較を貼り、同じ右上頂点像を消去する。
規約：四つの元の指定比較を保持。使われ方：共通の高次図式の実面の評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}
  (D M : TransportSquareDiagram p s f)

/-- 任意の底辺を持つ二実四角形の、元の四辺比較を貼った値は厳密に一致する。 -/
lemma TransportSquareDiagram.comparison_eq : D.comparison = M.comparison := by
  let A := D.rightComparison ≪≫ diagonalFiberTransport_sourceIso p D.bottomComparison s.right
  let A' := M.rightComparison ≪≫ diagonalFiberTransport_sourceIso p M.bottomComparison s.right
  let C := D.topComparison ≪≫ diagonalFiberTransport_sourceIso p D.leftComparison s.top
  let C' := M.topComparison ≪≫ diagonalFiberTransport_sourceIso p M.leftComparison s.top
  have hA : D.topRightIso M ≪≫ A' = A := by
    dsimp only [A, A']
    rw [← Iso.trans_assoc, D.rightComparison_naturality M, Iso.trans_assoc,
      diagonalFiberTransport_sourceIso_trans, D.bottomComparison_naturality M]
  have hC : D.topRightIso M ≪≫ C' = C := by
    dsimp only [C, C']
    rw [← Iso.trans_assoc, D.topComparison_naturality M, Iso.trans_assoc,
      diagonalFiberTransport_sourceIso_trans, D.leftComparison_naturality M]
  have h : A ≪≫ (A.symm ≪≫ C) = A ≪≫ (A'.symm ≪≫ C') := by
    calc
      A ≪≫ (A.symm ≪≫ C) = C := by simp
      _ = D.topRightIso M ≪≫ C' := hC.symm
      _ = (D.topRightIso M ≪≫ A') ≪≫ (A'.symm ≪≫ C') := by
        simp [Iso.trans_assoc]
      _ = A ≪≫ (A'.symm ≪≫ C') := by rw [hA]
  have h' := congrArg (fun e => A.symm ≪≫ e) h
  have heq : A.symm ≪≫ C = A'.symm ≪≫ C' := by
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using h'
  simpa only [A, A', C, C', TransportSquareDiagram.comparison, Iso.trans_assoc] using heq

end SerrePositivity.InfinityCategories.F2
