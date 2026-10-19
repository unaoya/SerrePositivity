module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackVertexOfData

/-!
概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
lemma laxPullbackVertexOfData_data {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : (laxPullback p q) _⦋0⦌) :
    laxPullbackVertexOfData p q (laxPullbackVertexData p q x) = x := by
  apply pullbackSimplex_ext (arrowEndpointPair C) (p ⊗ₘ q)
  · rw [laxPullbackVertexOfData, pullbackSimplex_fst]
    exact (intervalFunctorVertexEdgeEquiv C).symm_apply_apply _
  · rw [laxPullbackVertexOfData, pullbackSimplex_snd]
    rfl
/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
lemma laxPullbackVertexData_ofData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : LaxPullbackVertexData p q) :
    laxPullbackVertexData p q (laxPullbackVertexOfData p q x) = x := by
  apply LaxPullbackVertexData.ext
  · change ((pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (laxPullbackVertexOfData p q x)).1 = x.left
    rw [laxPullbackVertexOfData, pullbackSimplex_snd]
  · change ((pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (laxPullbackVertexOfData p q x)).2 = x.right
    rw [laxPullbackVertexOfData, pullbackSimplex_snd]
  · change intervalFunctorVertexEdge
      ((pullback.fst (arrowEndpointPair C) (p ⊗ₘ q)).app (Opposite.op ⦋0⦌)
      (laxPullbackVertexOfData p q x)) = x.arrow
    rw [laxPullbackVertexOfData, pullbackSimplex_fst]
    exact (intervalFunctorVertexEdgeEquiv C).apply_symm_apply _
/-- 概要：lax pullback の頂点と指定三つ組の全単射。
方針：二射影の回収と矢印の一次単体の往復を比較する。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def laxPullbackVertexEquiv {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullback p q) _⦋0⦌ ≃ LaxPullbackVertexData p q :=
  ⟨laxPullbackVertexData p q, laxPullbackVertexOfData p q,
    laxPullbackVertexOfData_data p q, laxPullbackVertexData_ofData p q⟩

end SerrePositivity.InfinityCategories.F2
