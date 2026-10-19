module
public import SerrePositivity.KST.ProExcision.IdealColumnBlockInclusion
public import SerrePositivity.KST.ProExcision.IdealRowMatrixAction

/-!
# 行の零埋めと右行列作用の実同変性

概要：通常の零埋め行と単位ブロック和が右行列作用と可換であることを証明する。
方針：有限和を二つのブロックに分け、後半の零成分を消去する。
規約：KST Proposition 4.14、SW92 §1.2。非可換な係数環。
使われ方：行側半直積の通常の rank 安定化。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：イデアル内の行の零埋めは単位ブロック和の右行列作用に同変。
方針：各列で前半・後半の有限和を評価する。
規約：SW92 §1.2、全行列と非可換係数。
使われ方：実行側の通常の有限 rank 遷移。 -/
lemma idealRowBlockInclusion_equivariant (J : TwoSidedIdeal R) (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    idealRowMatrixAction (n + m) J (MulOpposite.op (firstBlockMatrix n m M))
        ((columnBlockInclusion J n m).toMultiplicative v) =
      (columnBlockInclusion J n m).toMultiplicative
        (idealRowMatrixAction n J (MulOpposite.op M) v) := by
  change idealRowMatrixVecHom (n + m) J (firstBlockMatrix n m M)
    (columnBlockInclusion J n m v.toAdd) = columnBlockInclusion J n m
      (idealRowMatrixVecHom n J M v.toAdd)
  funext j
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases j with
  | inl j =>
    simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
    apply Subtype.ext
    change (∑ i, (columnBlockInclusion J n m v.toAdd i : R) *
      firstBlockMatrix n m M i (Fin.castAdd m j)) = ∑ i, (v.toAdd i : R) * M i j
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_left_left, firstBlockMatrix_right_left,
      columnBlockInclusion_left, columnBlockInclusion_right, zero_mul,
      Finset.sum_const_zero, add_zero]
    simp
  | inr j =>
    simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right]
    apply Subtype.ext
    change (∑ i, (columnBlockInclusion J n m v.toAdd i : R) *
      firstBlockMatrix n m M i (Fin.natAdd n j)) = 0
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_left_right, firstBlockMatrix_right_right,
      columnBlockInclusion_left, columnBlockInclusion_right, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    simp

end SerrePositivity.KST.ProExcision
