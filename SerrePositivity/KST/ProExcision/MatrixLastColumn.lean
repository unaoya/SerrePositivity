module
public import SerrePositivity.KST.ProExcision.TriangularHatGL

/-!
# 最終行が恒等行である行列の左上ブロックと最終列

概要：実三角行列の分解に使う二つの成分と積の公式を構成する。
方針：有限和を最後の添字と残りに分け、最終行の恒等条件で余分な項を消す。
規約：KST Claim 4.15 の半直積への因子化。係数環は非可換。
使われ方：T_{n,m+1} を T_{n,m} と列群へ分ける実射。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R] {N : ℕ}

/-- 概要：最後の行・列を除いた左上ブロック。
方針：castSucc による二つの添字の制限。
規約：KST Claim 4.15。使われ方：半直積の基底成分。 -/
def matrixDropLast (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin N) (Fin N) R := A.submatrix Fin.castSucc Fin.castSucc

/-- 概要：最後の対角成分を除いた最終列。
方針：行を castSucc、列を last に制限する。
規約：KST Claim 4.15。使われ方：半直積の列成分。 -/
def matrixLastColumn (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) : Fin N → R :=
  fun i ↦ A i.castSucc (Fin.last N)

/-- 概要：恒等行列の左上ブロックは恒等行列。
方針：単射な添字制限による単位行列の公式。
規約：KST Claim 4.15。使われ方：単位・逆のブロックの確認。 -/
lemma matrixDropLast_one : matrixDropLast (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) = 1 := by
  exact Matrix.submatrix_one Fin.castSucc (Fin.castSucc_injective _)

/-- 概要：恒等行列の最終列の前半は零。
方針：castSucc の添字は last と異なる。
規約：KST Claim 4.15。使われ方：半直積の単位。 -/
lemma matrixLastColumn_one : matrixLastColumn (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) = 0 := by
  funext i
  simp [matrixLastColumn]

/-- 概要：右因子の最終行が恒等行なら左上ブロックは積を保つ。
方針：行列積の有限和を最終添字で分ける。
規約：KST Claim 4.15、非可換な積の順を保つ。
使われ方：三角群の左上ブロックの群準同型。 -/
lemma matrixDropLast_mul (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hB : ∀ j, B (Fin.last N) j = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (Fin.last N) j) :
    matrixDropLast (A * B) = matrixDropLast A * matrixDropLast B := by
  apply Matrix.ext
  intro i j
  change (∑ k, A i.castSucc k * B k j.castSucc) = ∑ k : Fin N, _
  rw [Fin.sum_univ_castSucc, hB]
  simp [matrixDropLast, Matrix.submatrix_apply,
    Ne.symm (Fin.castSucc_ne_last j)]

/-- 概要：最終行が恒等行の右因子との積の最終列は半直積の加法則に従う。
方針：最後の和の項を左因子の最終列に同定する。
規約：KST Claim 4.15、列は左行列作用を受ける。
使われ方：実三角行列の半直積分解の積保存。 -/
lemma matrixLastColumn_mul (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hB : B (Fin.last N) (Fin.last N) = 1) :
    matrixLastColumn (A * B) = matrixLastColumn A + matrixDropLast A *ᵥ matrixLastColumn B := by
  funext i
  change (∑ k, A i.castSucc k * B k (Fin.last N)) =
    A i.castSucc (Fin.last N) + ∑ k : Fin N, _
  rw [Fin.sum_univ_castSucc, hB, mul_one, add_comm]
  rfl

end SerrePositivity.KST.ProExcision
