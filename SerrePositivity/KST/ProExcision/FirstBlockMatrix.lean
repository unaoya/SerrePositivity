module
public import SerrePositivity.KST.ProExcision.LeftMultiplier
public import Mathlib.Data.Matrix.Block

/-!
# first n 行に作用する非可逆なブロック対角行列

概要：任意の n×n 行列 M を diag(M,1) として周囲の行列環に入れる。
方針：直和のブロック行列を Fin の添字へ変更し、四つのブロックの成分を計算する。
規約：KST Lemma 4.16 の左行列作用。M の可逆性や可換性は不要。
使われ方：三角部分環と 1+S の群の外部モノイド作用。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：M と恒等行列を対角に持つ実ブロック行列。
方針：fromBlocks を Fin n ⊕ Fin m から Fin(n+m) に添字変更する。
規約：KST 4.16、左から行に作用させる乗数。
使われ方：一般の行列モノイドの作用の定義。 -/
def firstBlockMatrix (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + m)) (Fin (n + m)) R :=
  Matrix.reindexRingEquiv R finSumFinEquiv (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) R))

/-- 概要：左上ブロックは元の M。
方針：Fin の直和同値の左成分を評価する。
規約：KST 4.16。使われ方：first n 行の作用の成分。 -/
lemma firstBlockMatrix_left_left (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    firstBlockMatrix n m M (Fin.castAdd m i) (Fin.castAdd m j) = M i j := by
  change (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) R))
    (finSumFinEquiv.symm (Fin.castAdd m i)) (finSumFinEquiv.symm (Fin.castAdd m j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- 概要：右上の交差ブロックは零。
方針：Fin の直和同値の左右の成分を評価する。
規約：KST 4.16。使われ方：補助列への行作用の計算。 -/
lemma firstBlockMatrix_left_right (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (j : Fin m) :
    firstBlockMatrix n m M (Fin.castAdd m i) (Fin.natAdd n j) = 0 := by
  change (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) R))
    (finSumFinEquiv.symm (Fin.castAdd m i)) (finSumFinEquiv.symm (Fin.natAdd n j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- 概要：左下の交差ブロックは零。
方針：Fin の直和同値の右左の成分を評価する。
規約：KST 4.16。使われ方：三角部分の右吸収。 -/
lemma firstBlockMatrix_right_left (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) (i : Fin m) (j : Fin n) :
    firstBlockMatrix n m M (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  change (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) R))
    (finSumFinEquiv.symm (Fin.natAdd n i)) (finSumFinEquiv.symm (Fin.castAdd m j)) = _
  rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- 概要：右下ブロックは恒等行列。
方針：Fin の直和同値の右成分を評価する。
規約：KST 4.16。使われ方：first n 行以外の不変性。 -/
lemma firstBlockMatrix_right_right (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) (i j : Fin m) :
    firstBlockMatrix n m M (Fin.natAdd n i) (Fin.natAdd n j) = (1 : Matrix (Fin m) (Fin m) R) i j := by
  change (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) R))
    (finSumFinEquiv.symm (Fin.natAdd n i)) (finSumFinEquiv.symm (Fin.natAdd n j)) = _
  rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
  rfl

end SerrePositivity.KST.ProExcision
