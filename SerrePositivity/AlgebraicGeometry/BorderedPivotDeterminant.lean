module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdeal

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の単元ピボットに一行一列を加えた行列式。
方針：Schur 補元の行列式公式を最後の成分が一行一列の場合に適用する。
規約：この段階はピボットの可逆性を明示し、一般の正則な行列式の場合とは区別する。
使われ方：次次数の小行列式の消滅から、残る関係式を消去する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/--
概要：ピボット行列に一列・一行と交点の係数を加えた正方行列。
方針：最後の成分を Unit で添字付けして四つのブロックを組み合わせる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、ピボットの階数零も含む。
使われ方：一つ高い次数の小行列式を Schur 補元に比較する。
-/
def borderedPivotMatrix (A : Matrix ι ι R) (x b : ι → R) (y : R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks A (fun i _ => x i) (fun _ i => b i) (fun _ _ => y)

set_option backward.isDefEq.respectTransparency false in
/--
概要：可逆なピボットを持つ境界行列式は、ピボットの行列式と残余係数の積。
方針：Schur 補元の公式と一行一列の行列式を計算する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、逆行列は明示的な可逆性から与える。
使われ方：境界小行列式が零のときに関係式の残余を消す。
-/
theorem borderedPivotMatrix_det (A : Matrix ι ι R) [Invertible A]
    (x b : ι → R) (y : R) :
    (borderedPivotMatrix A x b y).det = A.det * (y - b ⬝ᵥ (⅟A *ᵥ x)) := by
  rw [borderedPivotMatrix, Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/--
概要：単元ピボットを持つ境界行列の行列式が零なら残余係数は零。
方針：境界行列式の積の公式で単元である行列式を消去する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基礎環の整域性は不要。
使われ方：残りの関係式がピボット関係式から生成されることを示す。
-/
theorem borderedPivotMatrix_residual_eq_zero (A : Matrix ι ι R) [Invertible A]
    (x b : ι → R) (y : R) (hdet : (borderedPivotMatrix A x b y).det = 0) :
    y - b ⬝ᵥ (⅟A *ᵥ x) = 0 := by
  rw [borderedPivotMatrix_det] at hdet
  exact (Matrix.isUnit_det_of_invertible A).mul_right_eq_zero.mp hdet

/--
概要：任意の有限添字集合で指定した小行列式は、その濃度の小行列式イデアルに属する。
方針：有限添字集合を Fin に移し、行と列を同じ同型で変換した行列式を比較する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、選択写像の単射性は不要。
使われ方：一行一列を追加した直和添字の境界行列を小行列式イデアルへ戻す。
-/
theorem det_submatrix_mem_matrixMinorIdeal_fintype {m n : Type*}
    (H : Matrix m n R) (r : ι → m) (c : ι → n) :
    (H.submatrix r c).det ∈ matrixMinorIdeal H (Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm
  have h := det_submatrix_mem_matrixMinorIdeal H (Fintype.card ι) (r ∘ e) (c ∘ e)
  change ((H.submatrix r c).submatrix e e).det ∈ matrixMinorIdeal H (Fintype.card ι) at h
  simpa only [Matrix.det_submatrix_equiv_self] using h

/--
概要：ピボットに任意の一行一列を追加した境界行列式は、一つ高い次数の小行列式イデアルに属する。
方針：境界行列を直和添字で指定した元の行列の小行列に同定する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、追加行・列の重複は許す。
使われ方：次次数の小行列式イデアルの消滅を Schur 補元へ適用する。
-/
theorem borderedPivotMatrix_mem_succ_minorIdeal {m n : Type*} {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (c : Fin k → n) (i : m) (j : n) :
    (borderedPivotMatrix (H.submatrix r c) (fun l => H (r l) j)
      (fun l => H i (c l)) (H i j)).det ∈ matrixMinorIdeal H (k + 1) := by
  let r' : Fin k ⊕ Unit → m := Sum.elim r (fun _ => i)
  let c' : Fin k ⊕ Unit → n := Sum.elim c (fun _ => j)
  have hmat : borderedPivotMatrix (H.submatrix r c) (fun l => H (r l) j)
      (fun l => H i (c l)) (H i j) = H.submatrix r' c' := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hmat]
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] using
    det_submatrix_mem_matrixMinorIdeal_fintype H r' c'

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
