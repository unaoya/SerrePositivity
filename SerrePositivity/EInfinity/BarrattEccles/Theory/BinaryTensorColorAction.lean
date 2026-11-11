module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColors
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# 二色の入力語の置換作用

## 概要
HA 3.2.4.7 の Schur 分解のため、位置の置換を二色の入力語に作用させる。

## 方針
位置ごとの色の関数に対する引き戻し作用を、指定全単射で移す。

## 規約
左作用は逆置換で引き戻す。左の色を false とする規約を保つ。

## 使われ方
固定した色の個数の軌道と、二色部分群から誘導した表示。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity

/-- 置換は、逆置換により各位置の色を引き戻して入力語に作用する。 -/
instance binaryTensorWordMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (BinaryTensorWord n) where
  smul σ w := binaryTensorWordOfColors n (fun i => binaryTensorWordColors n w (σ.symm i))
  one_smul w := by
    change binaryTensorWordOfColors n (fun i => binaryTensorWordColors n w i) = w
    exact binaryTensorWordOfColors_colors n w
  mul_smul σ τ w := by
    change binaryTensorWordOfColors n
      (fun i => binaryTensorWordColors n w ((σ * τ).symm i)) =
        binaryTensorWordOfColors n (fun i => binaryTensorWordColors n
          (binaryTensorWordOfColors n (fun j => binaryTensorWordColors n w (τ.symm j)))
          (σ.symm i))
    rw [binaryTensorWordColors_ofColors]
    rfl

/-- 置換した語の色は、逆置換による元の色の引き戻しである。 -/
@[simp]
lemma binaryTensorWordColors_smul (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) (i : Fin n) :
    binaryTensorWordColors n (σ • w) i = binaryTensorWordColors n w (σ.symm i) :=
  congrFun (binaryTensorWordColors_ofColors n _) i

/-- 入力語の中の左因子の個数。 -/
def binaryTensorWordLeftCount (n : ℕ) (w : BinaryTensorWord n) : ℕ :=
  ∑ i : Fin n, if binaryTensorWordColors n w i then 0 else 1

/-- 左因子の個数は、位置の置換によって変わらない。 -/
@[simp]
lemma binaryTensorWordLeftCount_smul (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) :
    binaryTensorWordLeftCount n (σ • w) = binaryTensorWordLeftCount n w := by
  simp only [binaryTensorWordLeftCount, binaryTensorWordColors_smul]
  exact Equiv.sum_comp σ.symm
    (fun i : Fin n => if binaryTensorWordColors n w i then (0 : ℕ) else 1)

end SerrePositivity.EInfinity
