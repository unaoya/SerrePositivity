module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# 二つの有限ブロックの置換

概要：Berger–Fresse §1.1.3 の反復 shuffle に使うブロック内の置換を定義する。
方針：有限和の各成分の置換を Fin(p+q) へ移送する。
規約：最初の p 個と残りの q 個をそれぞれ独立に置換する。
使われ方：反復 shuffle の置換の積と符号の積を比較する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：二つの有限ブロックを独立に置換する（Berger–Fresse §1.1.3）。
方針：sumCongr を標準の有限和の全単射で移送する。
規約：ブロック間の順序は交換しない。
使われ方：三入力の反復 shuffle 置換の内側の因子を表す。 -/
def shuffleBlockPermutation {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)

/-- 概要：ブロック置換の最初の成分での値（Berger–Fresse §1.1.3）。
方針：有限和の左成分で評価する。
規約：最初のブロックの位置は castAdd で表す。
使われ方：三入力の最初と二番目の色の置換を計算する。 -/
@[simp] lemma shuffleBlockPermutation_castAdd {p q : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) (a : Fin p) :
    shuffleBlockPermutation σ τ (Fin.castAdd q a) = Fin.castAdd q (σ a) := by
  simp [shuffleBlockPermutation]

/-- 概要：ブロック置換の最後の成分での値（Berger–Fresse §1.1.3）。
方針：有限和の右成分で評価する。
規約：最後のブロックの位置は natAdd で表す。
使われ方：三入力の二番目と三番目の色の置換を計算する。 -/
@[simp] lemma shuffleBlockPermutation_natAdd {p q : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) (a : Fin q) :
    shuffleBlockPermutation σ τ (Fin.natAdd p a) = Fin.natAdd p (τ a) := by
  simp [shuffleBlockPermutation]

/-- 概要：ブロック置換の符号は各ブロックの符号の積である（Berger–Fresse §1.1.3）。
方針：符号の移送不変性と sumCongr の符号の公式を使う。
規約：符号は整数の単元として取る。
使われ方：反復 shuffle の各段の符号の積を計算する。 -/
@[simp] lemma shuffleBlockPermutation_sign {p q : ℕ}
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    Equiv.Perm.sign (shuffleBlockPermutation σ τ) = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
  simp [shuffleBlockPermutation, Equiv.Perm.sign_sumCongr]

end SerrePositivity.EInfinity.BarrattEccles
