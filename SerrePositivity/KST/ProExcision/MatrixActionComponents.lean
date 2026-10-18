module
public import SerrePositivity.KST.ProExcision.IdealColumnEquivariance

/-!
# 実ブロック群の行列作用の成分

概要：行列作用の前半行・後半行と固定列を実成分で記述する。
方針：1+B(g−1) の式にブロック積の公式を適用する。
規約：KST Lemma 4.16 のブロック挿入と補助元の同変性。
使われ方：P の埋め込みと外部行列作用が可換であることの証明。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：実群の作用の first n 行は 1 からの差の左線形結合。
方針：実群の作用の値と first n 行の積の式を使う。
規約：KST 4.16。使われ方：ブロック埋め込みの同変性。 -/
lemma triangularBlockMatrixAction_firstRows (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (g : triangularBlockGroup n m J)
    (i : Fin n) (j : Fin (n + m)) :
    ((triangularBlockMatrixAction n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R)
        (Fin.castAdd m i) j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.castAdd m i) j +
        ∑ k, M i k * ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.castAdd m k) j -
          (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.castAdd m k) j) := by
  change ((triangularBlockMatrixEnd n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) _ _ = _
  rw [triangularBlockMatrixEnd_val]
  simp only [Matrix.add_apply, firstBlockMatrix_mul_firstRows, Matrix.sub_apply]

/-- 概要：実群の行列作用の残りの行はそのまま。
方針：後半行の差は変わらず、恒等成分を戻すと元の値になる。
規約：KST 4.16。使われ方：補助行の固定性。 -/
lemma triangularBlockMatrixAction_otherRows (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (g : triangularBlockGroup n m J)
    (i : Fin m) (j : Fin (n + m)) :
    ((triangularBlockMatrixAction n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R)
        (Fin.natAdd n i) j = (g.val : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.natAdd n i) j := by
  change ((triangularBlockMatrixEnd n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) _ _ = _
  rw [triangularBlockMatrixEnd_val]
  simp only [Matrix.add_apply, firstBlockMatrix_mul_otherRows, Matrix.sub_apply]
  abel

/-- 概要：行列作用は任意の固定列を保つ。
方針：固定列では 1 からの差が全て零であることを使う。
規約：KST 4.16。使われ方：P の追加補助列の不変性。 -/
lemma triangularBlockMatrixAction_preserves_fixed_column (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (g : triangularBlockGroup n m J) (j : Fin (n + m))
    (hj : ∀ i, (g.val : Matrix (Fin (n + m)) (Fin (n + m)) R) i j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j) (i : Fin (n + m)) :
    ((triangularBlockMatrixAction n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) i j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j := by
  change ((triangularBlockMatrixEnd n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) _ _ = _
  rw [triangularBlockMatrixEnd_val]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, hj,
    sub_self, mul_zero, Finset.sum_const_zero, add_zero]

end SerrePositivity.KST.ProExcision
