module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLiftRightNaturality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLiftTopNaturality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoComposition

/-!
概要：同じ底辺を固定した実四角形は、元の指定合成比較に同じ値を与える。
方針：左右辺と上辺の自然性を貼り、中間頂点の像を消去する。
規約：元の transportIso の選択を保持。使われ方：指定比較の幾何的合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
  {f : P ⟶ vertexFiber p a} (L M : TransportSquareLift p s f)

/-- 同じ底辺を固定した任意の実四角形の、三辺による指定比較値は一致する。 -/
lemma TransportSquareLift.comparison_eq : L.comparison = M.comparison := by
  have h : L.rightComparison ≪≫ L.comparison = L.rightComparison ≪≫ M.comparison := by
    calc
      L.rightComparison ≪≫ L.comparison = L.topComparison ≪≫
          diagonalFiberTransport_sourceIso p L.leftComparison s.top := by
        simp [TransportSquareLift.comparison, ← Iso.trans_assoc]
      _ = L.topComparison ≪≫
          (diagonalFiberTransport_sourceIso p (L.topLeftIso M) s.top ≪≫
            diagonalFiberTransport_sourceIso p M.leftComparison s.top) := by
        rw [diagonalFiberTransport_sourceIso_trans, L.leftComparison_naturality M]
      _ = (L.topRightIso M ≪≫ M.topComparison) ≪≫
          diagonalFiberTransport_sourceIso p M.leftComparison s.top := by
        rw [← Iso.trans_assoc, ← L.topComparison_naturality M]
      _ = L.rightComparison ≪≫ M.comparison := by
        rw [← L.rightComparison_naturality M]
        simp [TransportSquareLift.comparison, Iso.trans_assoc]
  have h' := congrArg (fun e => L.rightComparison.symm ≪≫ e) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using h'

/-- 任意の実持ち上げから計算した値は、元の選択済み transportIso に一致する。 -/
lemma TransportSquareLift.comparison_eq_transportIso : L.comparison = s.transportIso p f :=
  (L.comparison_eq (transportSquareCanonicalLift p s f)).trans
    (transportSquareCanonicalComparison_eq_transportIso p s f)

end SerrePositivity.InfinityCategories.F2
