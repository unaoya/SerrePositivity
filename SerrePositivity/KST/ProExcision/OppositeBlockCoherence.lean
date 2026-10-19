module
public import SerrePositivity.KST.ProExcision.OppositeColumnRowEquivariance
public import SerrePositivity.KST.ProExcision.SimplicialRowBlockInclusion

/-!
# 反対転置と通常のブロック安定化の実整合

概要：反対転置の行列・ベクトル比較が通常のブロック和・零埋めと可換であることを示す。
方針：二つの添字ブロックに分け、零と単位元の保存を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：行側安定零化への実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable (J : Type u) [NonUnitalRing J]

/-- 概要：実反対転置は通常の単位ブロック和と可換。
方針：前半・後半の四つの行列ブロックで実単位化同型を評価する。
規約：SW92 §1.2、非可換な行列。使われ方：ĜL の通常の安定化との比較。 -/
lemma integerUnitizationMatrixOpEquiv_block (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ Jᵐᵒᵖ)) :
    integerUnitizationMatrixOpEquiv J (n + m) (firstBlockMatrix n m A) =
      MulOpposite.op (firstBlockMatrix n m
        (MulOpposite.unop (integerUnitizationMatrixOpEquiv J n A))) := by
  apply MulOpposite.unop_injective
  apply Matrix.ext
  intro i j
  change MulOpposite.unop (integerUnitizationOpEquiv J (firstBlockMatrix n m A j i)) =
    firstBlockMatrix n m (MulOpposite.unop (integerUnitizationMatrixOpEquiv J n A)) i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases i <;> cases j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      firstBlockMatrix_left_left, firstBlockMatrix_left_right,
      firstBlockMatrix_right_left, firstBlockMatrix_right_right, map_zero, MulOpposite.unop_zero]
  · rfl
  · simp only [Matrix.one_apply]
    split_ifs with h h'
    all_goals simp_all [eq_comm]

/-- 概要：実反対核イデアル比較は通常の零埋めベクトルと可換。
方針：前半は定義で一致し、後半は実加法同型の零保存を使う。
規約：SW92 §1.2。使われ方：行側と列側の通常の rank 遷移の整合。 -/
lemma integerUnitizationIdealOpVector_block (n m : ℕ)
    (v : Multiplicative (Fin n → integerUnitizationIdeal Jᵐᵒᵖ)) :
    integerUnitizationIdealOpVectorMulEquiv J (n + m)
        ((columnBlockInclusion (integerUnitizationIdeal Jᵐᵒᵖ) n m).toMultiplicative v) =
      (columnBlockInclusion (integerUnitizationIdeal J) n m).toMultiplicative
        (integerUnitizationIdealOpVectorMulEquiv J n v) := by
  change (fun i ↦ integerUnitizationIdealOpAddEquiv J
      (columnBlockInclusion (integerUnitizationIdeal Jᵐᵒᵖ) n m v.toAdd i)) =
    columnBlockInclusion (integerUnitizationIdeal J) n m
      (fun i ↦ integerUnitizationIdealOpAddEquiv J (v.toAdd i))
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i => simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
  | inr i => simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right, map_zero]

end SerrePositivity.KST.ProExcision
