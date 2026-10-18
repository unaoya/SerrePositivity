module
public import SerrePositivity.KST.ProExcision.FirstBlockPreservation

/-!
# 実三角ブロック群への行列モノイドの作用

概要：first n 行への一般の行列の作用を、行列モノイドから群の自己準同型への準同型に束ねる。
方針：diag(M,1) の単位・積の保存と、1+B(g−1) の実成分の公式を使う。
規約：KST Lemma 4.16 の外部 M_{n,n} 同変性、可逆性を仮定しない。
使われ方：P,Q,H と補助元 u、μ、φ、ψ の同変性。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：左作用のブロック対角行列は単位を保つ。
方針：両対角の恒等成分と添字変更の単位保存。
規約：KST 4.16。使われ方：作用の単位法則。 -/
lemma firstBlockMatrix_one (n m : ℕ) : firstBlockMatrix n m (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  dsimp only [firstBlockMatrix]
  rw [Matrix.fromBlocks_one, map_one]

/-- 概要：左作用のブロック対角行列は積を保つ。
方針：ブロック行列の積と添字変更の乗法保存。
規約：KST 4.16。使われ方：外部行列作用の合成法則。 -/
lemma firstBlockMatrix_mul (n m : ℕ) (M N : Matrix (Fin n) (Fin n) R) :
    firstBlockMatrix n m (M * N) = firstBlockMatrix n m M * firstBlockMatrix n m N := by
  dsimp only [firstBlockMatrix]
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

/-- 概要：実群の行列作用の値は 1+diag(M,1)(g−1)。
方針：差の単位部分群への持ち上げの定義を評価する。
規約：KST 4.16、周囲の非可換行列環の等式。
使われ方：作用の法則と φ、ψ、u の同変性の成分計算。 -/
lemma triangularBlockMatrixEnd_val (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (g : triangularBlockGroup n m J) :
    ((triangularBlockMatrixEnd n m J M g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) =
      1 + firstBlockMatrix n m M * ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) R) - 1) := rfl

/-- 概要：実三角ブロック群の外部行列モノイドの作用。
方針：実成分の公式から単位作用と合成作用の法則を証明する。
規約：KST Lemma 4.16 の行列同変性、全行列を許す。
使われ方：Construction A.5 の外部 G として渡す実作用。 -/
def triangularBlockMatrixAction (n m : ℕ) (J : TwoSidedIdeal R) :
    Matrix (Fin n) (Fin n) R →* Monoid.End (triangularBlockGroup n m J) where
  toFun := triangularBlockMatrixEnd n m J
  map_one' := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    change ((triangularBlockMatrixEnd n m J 1 g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) = _
    rw [triangularBlockMatrixEnd_val, firstBlockMatrix_one, one_mul]
    abel
  map_mul' M N := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    change ((triangularBlockMatrixEnd n m J (M * N) g).val : Matrix (Fin (n + m)) (Fin (n + m)) R) =
      ((triangularBlockMatrixEnd n m J M (triangularBlockMatrixEnd n m J N g)).val :
        Matrix (Fin (n + m)) (Fin (n + m)) R)
    rw [triangularBlockMatrixEnd_val, triangularBlockMatrixEnd_val, triangularBlockMatrixEnd_val,
      firstBlockMatrix_mul, add_sub_cancel_left, mul_assoc]

end SerrePositivity.KST.ProExcision
