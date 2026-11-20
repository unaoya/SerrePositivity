module

public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdeal

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の表示行列の線形変換と小行列式。
方針：行列式の多重線形性を使って積行列の小行列式を展開する。
規約：行列の積で和を取る内側の添字集合だけに有限性を課す。
使われ方：Fitting の計算で表示の行・列を変換する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] {l m n : Type*}

/--
概要：行の線形結合で小行列式イデアルは大きくならない。
方針：各行の有限和を行列式の多重線形性で展開する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行列を左から掛ける。
使われ方：生成元側の表示変換と小行列式の比較。
-/
theorem matrixMinorIdeal_mul_left_le [Fintype m]
    (P : Matrix l m R) (A : Matrix m n R) (k : ℕ) :
    matrixMinorIdeal (P * A) k ≤ matrixMinorIdeal A k := by
  classical
  apply Ideal.span_le.mpr
  rintro x ⟨⟨r, c⟩, rfl⟩
  let F : MultilinearMap R (fun _ : Fin k => Fin k → R) R :=
    Matrix.detRowAlternating.toMultilinearMap
  have hrows : (P * A).submatrix r c =
      fun i : Fin k => ∑ t : m, P (r i) t • (fun j : Fin k => A t (c j)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  change F ((P * A).submatrix r c) ∈ matrixMinorIdeal A k
  rw [hrows, F.map_sum]
  apply (matrixMinorIdeal A k).sum_mem
  intro a _
  rw [F.map_smul_univ]
  exact (matrixMinorIdeal A k).smul_mem _ (det_submatrix_mem_matrixMinorIdeal A k a c)

/--
概要：列の線形結合で小行列式イデアルは大きくならない。
方針：転置して行の線形結合の場合を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行列を右から掛ける。
使われ方：関係式側の表示変換と小行列式の比較。
-/
theorem matrixMinorIdeal_mul_right_le [Fintype n]
    (A : Matrix m n R) (P : Matrix n l R) (k : ℕ) :
    matrixMinorIdeal (A * P) k ≤ matrixMinorIdeal A k := by
  have h := matrixMinorIdeal_mul_left_le P.transpose A.transpose k
  simpa only [← Matrix.transpose_mul, matrixMinorIdeal_transpose] using h

/--
概要：左逆元を持つ行変換は小行列式イデアルを保つ。
方針：変換とその左逆元についての包含を双方向に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、正方行列の左逆元を入力する。
使われ方：生成元の可逆な変更に関する表示行列の不変性。
-/
theorem matrixMinorIdeal_mul_left_eq [Fintype m] [DecidableEq m]
    (A : Matrix m n R) (P Q : Matrix m m R) (hQP : Q * P = 1) (k : ℕ) :
    matrixMinorIdeal (P * A) k = matrixMinorIdeal A k := by
  apply le_antisymm (matrixMinorIdeal_mul_left_le P A k)
  have h := matrixMinorIdeal_mul_left_le Q (P * A) k
  simpa only [← Matrix.mul_assoc, hQP, Matrix.one_mul] using h

/--
概要：右逆元を持つ列変換は小行列式イデアルを保つ。
方針：変換とその右逆元についての包含を双方向に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、正方行列の右逆元を入力する。
使われ方：関係式の可逆な変更に関する表示行列の不変性。
-/
theorem matrixMinorIdeal_mul_right_eq [Fintype n] [DecidableEq n]
    (A : Matrix m n R) (P Q : Matrix n n R) (hPQ : P * Q = 1) (k : ℕ) :
    matrixMinorIdeal (A * P) k = matrixMinorIdeal A k := by
  apply le_antisymm (matrixMinorIdeal_mul_right_le A P k)
  have h := matrixMinorIdeal_mul_right_le (A * P) Q k
  simpa only [Matrix.mul_assoc, hPQ, Matrix.mul_one] using h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
