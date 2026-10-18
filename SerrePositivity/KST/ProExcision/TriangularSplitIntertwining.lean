module
public import SerrePositivity.KST.ProExcision.TriangularLastColumn
public import SerrePositivity.KST.ProExcision.FirstBlockLastColumn
public import SerrePositivity.KST.ProExcision.TriangularGLProduct

/-!
# 外部行列作用と最終列分解の交換則

概要：三角群の作用の交換則を左上ブロックと最終列へ分ける。
方針：実行列の交換則へ二つの制限を適用し、最終行と単位ブロック和の公式を使う。
規約：KST Claim 4.15、外部行列の可逆性を要求しない。
使われ方：列群を含む一般線形半直積への実射の乗法保存。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：三角群の外部作用の左上ブロックは小さい単位ブロック和との交換則を満たす。
方針：全行列の交換則に左上ブロックの制限を適用する。
規約：KST Claim 4.15。使われ方：実半直積比較の基底の積。 -/
lemma triangularAction_dropLast_intertwining (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (t : triangularBlockGroup n (m + 1) J) :
    matrixDropLast (triangularBlockMatrixAction n (m + 1) J M t).val.val * firstBlockMatrix n m M =
      firstBlockMatrix n m M * matrixDropLast t.val.val := by
  have h := congrArg matrixDropLast
    (triangularBlockMatrixAction_intertwining n (m + 1) J M t)
  rw [matrixDropLast_mul _ _ (firstBlockMatrix_lastRow n m M),
    matrixDropLast_mul _ _ (triangularBlockGroup_lastRow n m J t),
    firstBlockMatrix_dropLast] at h
  exact h

/-- 概要：三角群の外部作用の最終列は小さい単位ブロック和の列作用に一致する。
方針：全行列の交換則に最終列を適用し、ブロック和の最終列が零であることを使う。
規約：KST Claim 4.15。使われ方：実半直積比較の列の積。 -/
lemma triangularAction_lastColumn (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (t : triangularBlockGroup n (m + 1) J) :
    matrixLastColumn (triangularBlockMatrixAction n (m + 1) J M t).val.val =
      firstBlockMatrix n m M *ᵥ matrixLastColumn t.val.val := by
  have h := congrArg matrixLastColumn
    (triangularBlockMatrixAction_intertwining n (m + 1) J M t)
  have hB : firstBlockMatrix n (m + 1) M (Fin.last (n + m)) (Fin.last (n + m)) = 1 := by
    simpa using firstBlockMatrix_lastRow n m M (Fin.last (n + m))
  have ht : t.val.val (Fin.last (n + m)) (Fin.last (n + m)) = 1 := by
    simpa using triangularBlockGroup_lastRow n m J t (Fin.last (n + m))
  rw [matrixLastColumn_mul _ _ hB, matrixLastColumn_mul _ _ ht,
    firstBlockMatrix_lastColumn, firstBlockMatrix_dropLast] at h
  simpa only [Matrix.mulVec_zero, add_zero, zero_add] using h

end SerrePositivity.KST.ProExcision
