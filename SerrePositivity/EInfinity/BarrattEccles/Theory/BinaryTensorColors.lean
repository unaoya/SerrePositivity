module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorWords
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# 入力語の色の関数

## 概要
HA 3.2.4.7 の色付き Schur 分解に向け、再帰的な入力語を位置ごとの色へ同定する。

## 方針
先頭と尾の再帰で二つの写像を作り、相互逆を示す。

## 規約
左因子を false、右因子を true とする。位置の番号は先頭から数える。

## 使われ方
二色の語の置換作用と、色の数による分解の添字。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity

/-- 再帰的な語を位置ごとの色の関数へ送る。 -/
def binaryTensorWordColors : ∀ n, BinaryTensorWord n → Fin n → Bool
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, .inl w => Fin.cons false (binaryTensorWordColors n w)
  | n + 1, .inr w => Fin.cons true (binaryTensorWordColors n w)

/-- 色の関数から再帰的な語を復元する。 -/
def binaryTensorWordOfColors : ∀ n, (Fin n → Bool) → BinaryTensorWord n
  | 0, _ => PUnit.unit
  | n + 1, f => if f 0 then .inr (binaryTensorWordOfColors n (fun i => f i.succ))
      else .inl (binaryTensorWordOfColors n (fun i => f i.succ))

/-- 色を読み取ってから復元すると元の語となる。 -/
@[simp]
lemma binaryTensorWordOfColors_colors : ∀ n (w : BinaryTensorWord n),
    binaryTensorWordOfColors n (binaryTensorWordColors n w) = w := by
  intro n
  induction n with
  | zero => intro w; cases w; rfl
  | succ n ih =>
    intro w
    cases w <;> simp [binaryTensorWordOfColors, binaryTensorWordColors, ih] <;> rfl

/-- 語を復元して色を読み取ると元の色の関数となる。 -/
@[simp]
lemma binaryTensorWordColors_ofColors : ∀ n (f : Fin n → Bool),
    binaryTensorWordColors n (binaryTensorWordOfColors n f) = f := by
  intro n
  induction n with
  | zero => intro f; funext i; exact Fin.elim0 i
  | succ n ih =>
    intro f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases h : f 0 <;> simp [binaryTensorWordOfColors, binaryTensorWordColors, h]
    · cases h : f 0 <;>
        simpa [binaryTensorWordOfColors, binaryTensorWordColors, h] using
          congrFun (ih (fun j => f j.succ)) j

/-- 再帰的な入力語と、位置ごとの色の関数の指定全単射。 -/
def binaryTensorWordColorsEquiv (n : ℕ) : BinaryTensorWord n ≃ (Fin n → Bool) where
  toFun := binaryTensorWordColors n
  invFun := binaryTensorWordOfColors n
  left_inv := binaryTensorWordOfColors_colors n
  right_inv := binaryTensorWordColors_ofColors n

/-- 色を保つかどうかの判定に使う、入力語の決定可能な等号。 -/
instance binaryTensorWordDecidableEq (n : ℕ) : DecidableEq (BinaryTensorWord n) :=
  (binaryTensorWordColorsEquiv n).injective.decidableEq

end SerrePositivity.EInfinity
