module
public import SerrePositivity.KST.ProExcision.BlockPatternNaturality
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 補助座標を挿入する実行列の準同型

概要：任意の位置に恒等行・列を挿入する行列単位群の準同型を構成する。
方針：Option による恒等成分の追加と Fin の指定点を抜く同値による添字変更を使う。
規約：KST Lemma 4.16 の n,m−1,1,1 のブロック配置。
使われ方：P の小さい三角ブロック群を H の補助行・列を固定する部分に埋め込む。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：Option の none に恒等な一成分を加える行列。
方針：some のブロックを元の行列、交差成分を零にする。
規約：KST 4.16 の補助行・列の挿入。
使われ方：指定した Fin の位置への恒等成分の追加。 -/
def optionMatrixExtension {κ : Type v} (M : Matrix κ κ R) : Matrix (Option κ) (Option κ) R
  | some i, some j => M i j
  | none, none => 1
  | _, _ => 0

/-- 概要：恒等成分の追加は行列の乗法モノイドの準同型。
方針：Option の添字の各場合に有限和を計算する。
規約：KST 4.16、環準同型とは主張しない。
使われ方：単位群への実準同型の誘導。 -/
def optionMatrixExtensionHom (κ : Type v) [Fintype κ] [DecidableEq κ] :
    Matrix κ κ R →* Matrix (Option κ) (Option κ) R where
  toFun := optionMatrixExtension
  map_one' := by
    ext i j
    cases i <;> cases j <;> simp [optionMatrixExtension, Matrix.one_apply]
  map_mul' M N := by
    ext i j
    cases i <;> cases j <;>
      simp [optionMatrixExtension, Matrix.mul_apply, Fintype.sum_option]

/-- 概要：Fin の指定した位置 p に恒等な行・列を挿入する行列準同型。
方針：Option の追加を指定点 p を抜く同値に沿って添字変更する。
規約：KST 4.16、元の座標は p.succAbove で埋め込む。
使われ方：小さい帰納段階の P の実ブロック埋め込み。 -/
def matrixInsertionHom {N : ℕ} (p : Fin (N + 1)) :
    Matrix (Fin N) (Fin N) R →* Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  ((Matrix.reindexRingEquiv R (finSuccEquiv' p).symm).toMonoidHom).comp
    (optionMatrixExtensionHom (R := R) (Fin N))

/-- 概要：恒等成分の挿入は行列単位群の準同型を誘導する。
方針：行列モノイドの準同型を単位へ適用する。
規約：KST 4.16、逆行列も同じ挿入で与えられる。
使われ方：P の群準同型としての実埋め込み。 -/
def matrixInsertionUnits {N : ℕ} (p : Fin (N + 1)) :
    (Matrix (Fin N) (Fin N) R)ˣ →* (Matrix (Fin (N + 1)) (Fin (N + 1)) R)ˣ :=
  Units.map (matrixInsertionHom p)

/-- 概要：挿入した行列の元の成分はそのまま保たれる。
方針：指定点を抜く同値と succAbove の互いの逆を使う。
規約：KST 4.16。使われ方：三角条件と係数イデアルの保存。 -/
lemma matrixInsertion_succAbove {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    matrixInsertionHom p M (p.succAbove i) (p.succAbove j) = M i j := by
  change optionMatrixExtension M ((finSuccEquiv' p) (p.succAbove i))
    ((finSuccEquiv' p) (p.succAbove j)) = _
  rw [finSuccEquiv'_succAbove, finSuccEquiv'_succAbove]
  rfl

/-- 概要：挿入した対角成分は 1。
方針：指定点は Option の none に対応する。
規約：KST 4.16。使われ方：追加座標の固定性。 -/
lemma matrixInsertion_self {N : ℕ} (p : Fin (N + 1)) (M : Matrix (Fin N) (Fin N) R) :
    matrixInsertionHom p M p p = 1 := by
  change optionMatrixExtension M ((finSuccEquiv' p) p) ((finSuccEquiv' p) p) = _
  rw [finSuccEquiv'_at]
  rfl

/-- 概要：挿入した補助行の他の成分は零。
方針：Option の none と some の交差成分を評価する。
規約：KST 4.16。使われ方：P の埋め込みの固定補助行。 -/
lemma matrixInsertion_row {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (j : Fin N) :
    matrixInsertionHom p M p (p.succAbove j) = 0 := by
  change optionMatrixExtension M ((finSuccEquiv' p) p) ((finSuccEquiv' p) (p.succAbove j)) = _
  rw [finSuccEquiv'_at, finSuccEquiv'_succAbove]
  rfl

/-- 概要：挿入した補助列の他の成分は零。
方針：Option の some と none の交差成分を評価する。
規約：KST 4.16。使われ方：P の埋め込みの補助列。 -/
lemma matrixInsertion_column {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    matrixInsertionHom p M (p.succAbove i) p = 0 := by
  change optionMatrixExtension M ((finSuccEquiv' p) (p.succAbove i)) ((finSuccEquiv' p) p) = _
  rw [finSuccEquiv'_succAbove, finSuccEquiv'_at]
  rfl

/-- 概要：既存成分の 1 からの差も恒等成分の挿入で保たれる。
方針：元の成分の公式と succAbove の単射性を使う。
規約：KST 4.16。使われ方：三角部分環の所属の移送。 -/
lemma matrixInsertion_difference_succAbove {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (matrixInsertionHom p M - 1) (p.succAbove i) (p.succAbove j) = (M - 1) i j := by
  simp only [Matrix.sub_apply, matrixInsertion_succAbove, Matrix.one_apply,
    Fin.succAbove_right_injective.eq_iff]

end SerrePositivity.KST.ProExcision
