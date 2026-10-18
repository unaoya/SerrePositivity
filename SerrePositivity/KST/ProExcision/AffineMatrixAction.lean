module
public import SerrePositivity.KST.ProExcision.AuxiliaryUnitAction

/-!
# 行列作用の周囲環でのアフィン公式

概要：1+B(A−1) の前半行・後半行・固定列を任意の周囲行列で計算する。
方針：行列積の既存のブロック成分公式を使う。
規約：KST Lemma 4.16 のブロック埋め込みの同変性。
使われ方：実群の挿入と全行列作用の可換性を群の所属条件から独立に証明する。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：任意の周囲行列に適用する 1+B(A−1) の式。
方針：実群作用と同じ式を周囲の行列環で定義する。
規約：KST 4.16。使われ方：挿入との成分比較。 -/
def affineMatrixAction (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) : Matrix (Fin (n + m)) (Fin (n + m)) R :=
  1 + firstBlockMatrix n m M * (A - 1)

/-- 概要：アフィン作用の first n 行は差の線形結合。
方針：前半行の左行列積の公式。
規約：KST 4.16。使われ方：既存座標の挿入との比較。 -/
lemma affineMatrixAction_firstRows (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) (i : Fin n) (j : Fin (n + m)) :
    affineMatrixAction n m M A (Fin.castAdd m i) j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.castAdd m i) j +
        ∑ k, M i k * ((A - 1) (Fin.castAdd m k) j) := by
  simp only [affineMatrixAction, Matrix.add_apply, firstBlockMatrix_mul_firstRows]

/-- 概要：前半以外の任意の行はアフィン作用で不変。
方針：添字の直和分解で後半に属することを確認する。
規約：KST 4.16。使われ方：挿入した補助行と元の補助行の一致。 -/
lemma affineMatrixAction_otherRows (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) (i j : Fin (n + m)) (hi : n ≤ i.val) :
    affineMatrixAction n m M A i j = A i j := by
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i =>
    change n ≤ i.val at hi
    have h := i.isLt
    omega
  | inr i =>
    simp only [finSumFinEquiv_apply_right, affineMatrixAction, Matrix.add_apply,
      firstBlockMatrix_mul_otherRows, Matrix.sub_apply]
    abel

/-- 概要：アフィン作用は任意の固定列を保つ。
方針：その列の全ての差が零であることを使う。
規約：KST 4.16。使われ方：挿入した補助列の固定性。 -/
lemma affineMatrixAction_fixed_column (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) (j : Fin (n + m))
    (hj : ∀ i, A i j = (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j) (i : Fin (n + m)) :
    affineMatrixAction n m M A i j = (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j := by
  simp only [affineMatrixAction, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, hj,
    sub_self, mul_zero, Finset.sum_const_zero, add_zero]

end SerrePositivity.KST.ProExcision
