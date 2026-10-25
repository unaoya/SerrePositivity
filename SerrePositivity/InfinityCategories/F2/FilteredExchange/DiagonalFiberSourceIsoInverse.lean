module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoComposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoIdentity

/-!
概要：元の始点同型の対角輸送は、同じ同型の逆を保つ。
方針：合成と恒等の保存から、元の指定比較の逆を回収する。
規約：選択済み sourceIso を使う。使われ方：四面の貼り合わせの中間因子消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の sourceIso は元の始点同型の逆を保持する。 -/
lemma diagonalFiberTransport_sourceIso_symm {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g)
    (c : P ⟶ intervalMappingSpace a b) :
    diagonalFiberTransport_sourceIso p e.symm c =
      (diagonalFiberTransport_sourceIso p e c).symm := by
  have h := diagonalFiberTransport_sourceIso_trans p e e.symm c
  rw [Iso.self_symm_id, diagonalFiberTransport_sourceIso_refl] at h
  have k := congrArg (fun t => (diagonalFiberTransport_sourceIso p e c).symm ≪≫ t) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans, Iso.trans_refl] using k

end SerrePositivity.InfinityCategories.F2
