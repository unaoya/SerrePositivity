module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
/-!
概要：dg 関手と実後続関手による閉辺の像の可逆性を、同じ閉射の像で計算する。
方針：dg 関手による実閉辺の全一次単体等式に、後続関手を適用する。
規約：両端の表示輸送を保つ。使われ方：K-flat 入力上の通常 kernel tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type v) [DGCategory R C] [DGCategory R E]
/-- 閉辺の dg 像を元の実辺へ同定した後で、任意の後続関手による可逆性を計算する。 -/
lemma dgClosedEdge_postcomposition_isInvertible_iff (F : DGFunctor R C E)
    {Y : SSet.{max u v}} (q : dgNerve R E ⟶ Y)
    {M N : ClosedCategory R C} (f : M ⟶ N) :
    IsInvertibleEdge ((dgClosedEdge R C f).map ((truncation 2).map (dgNerve.map F ≫ q))) ↔
      IsInvertibleEdge
        ((edgeOfSimplex (dgClosedEdge R E (F.onClosed.map f)).edge).map
          ((truncation 2).map q)) := by
  apply isInvertibleEdge_congr (X := Y)
  exact congrArg (fun t => q.app (Opposite.op ⦋1⦌) t) (dgClosedEdge_map R C F f)
end SerrePositivity.InfinityCategories
