module
public import SerrePositivity.KST.ProExcision.FirstBlockMatrix

/-!
# 左ブロック行列による三角成分への乗法

概要：diag(M,1) の左積と右積を first n 行・列と残りの成分に分けて計算する。
方針：Fin の有限和を二つのブロックへ分解する。
規約：KST Lemma 4.16 の非可換な左行列作用。
使われ方：三角部分環の保存と X·diag(M,1)=X の確認。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：左積の first n 行は M による線形結合。
方針：有限和を二つのブロックに分け、交差零成分を消す。
規約：KST 4.16。使われ方：列ベクトルの左行列作用との一致。 -/
lemma firstBlockMatrix_mul_firstRows (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) (i : Fin n) (j : Fin (n + m)) :
    (firstBlockMatrix n m M * A) (Fin.castAdd m i) j = ∑ k, M i k * A (Fin.castAdd m k) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp only [firstBlockMatrix_left_left, firstBlockMatrix_left_right, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- 概要：左積の残りの行はそのまま保たれる。
方針：右下ブロックの恒等行列で和を評価する。
規約：KST 4.16。使われ方：補助行の不変性。 -/
lemma firstBlockMatrix_mul_otherRows (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) (i : Fin m) (j : Fin (n + m)) :
    (firstBlockMatrix n m M * A) (Fin.natAdd n i) j = A (Fin.natAdd n i) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [firstBlockMatrix_right_left, firstBlockMatrix_right_right, Matrix.one_apply]

/-- 概要：first n 列が零なら右から diag(M,1) を掛けても変わらない。
方針：first n 列への和は零、残りの列への和は恒等行列で評価する。
規約：KST 4.16 の三角部分の右吸収、M の可逆性は不要。
使われ方：左作用が非単位環準同型となる乗法の計算。 -/
lemma firstBlockMatrix_right_absorbed (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R)
    (hA : ∀ i k, A i (Fin.castAdd m k) = 0) : A * firstBlockMatrix n m M = A := by
  ext i j
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases j with
  | inl j =>
    simp only [finSumFinEquiv_apply_left]
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [firstBlockMatrix_left_left, firstBlockMatrix_right_left, hA]
  | inr j =>
    simp only [finSumFinEquiv_apply_right]
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [firstBlockMatrix_left_right, firstBlockMatrix_right_right, Matrix.one_apply]

end SerrePositivity.KST.ProExcision
