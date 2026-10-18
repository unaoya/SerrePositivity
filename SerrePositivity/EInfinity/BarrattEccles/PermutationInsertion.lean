module

public import Mathlib.GroupTheory.Perm.Fin

/-!
# 置換の位置の挿入・削除と signature

概要：Berger–Fresse §1.1.3 の shuffle の辺の削除に必要な signature の変化を扱う。
方針：指定位置を先頭に移す巡回置換を介して、値の挿入を構成する。
規約：入力位置 j と出力位置 a の順序を保つ挿入に対し符号は (−1)^(a+j) 倍となる。
使われ方：同方向の境界面の符号を一つ小さい shuffle の符号と比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：置換に入力位置 j と出力位置 a の対応を一つ挿入する（Berger–Fresse §1.1.3）。
方針：j を先頭へ移し、小さい置換を適用してから先頭を a へ戻す。
規約：残りの入力と出力はそれぞれの順序を保って詰める。
使われ方：辺の挿入前後の shuffle 置換を比較する。 -/
def insertPermutation {N : ℕ} (j a : Fin (N + 1)) (σ : Equiv.Perm (Fin N)) :
    Equiv.Perm (Fin (N + 1)) :=
  a.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * j.cycleRange

/-- 概要：挿入された入力 j は挿入された出力 a へ移る（Berger–Fresse §1.1.3）。
方針：先頭の位置における巡回置換と置換の拡張の公式を使う。
規約：残りの置換の値には依存しない。
使われ方：指定辺を持つ shuffle の置換の値を計算する。 -/
@[simp] lemma insertPermutation_at {N : ℕ} (j a : Fin (N + 1)) (σ : Equiv.Perm (Fin N)) :
    insertPermutation j a σ j = a := by
  simp [insertPermutation]

/-- 概要：挿入位置以外では小さい置換を succAbove で移した値となる（Berger–Fresse §1.1.3）。
方針：巡回置換が succAbove を後続位置へ送る公式を使う。
規約：入力側では j、出力側では a を飛ばす。
使われ方：辺を削除した shuffle の置換の比較を頂点ごとに行う。 -/
@[simp] lemma insertPermutation_succAbove {N : ℕ} (j a : Fin (N + 1))
    (σ : Equiv.Perm (Fin N)) (x : Fin N) :
    insertPermutation j a σ (j.succAbove x) = a.succAbove (σ x) := by
  simp [insertPermutation]

/-- 概要：入力 j とその像を除去した置換（Berger–Fresse §1.1.3）。
方針：一点を除いた入力と出力の間の置換を昇順の同値で Fin N に戻す。
規約：入力・出力の残った順序を保つ削除である。
使われ方：大きい shuffle 置換を辺の削除後の置換へ移す。 -/
def deletePermutation {N : ℕ} (σ : Equiv.Perm (Fin (N + 1))) (j : Fin (N + 1)) :
    Equiv.Perm (Fin N) :=
  (finSuccAboveEquiv j).trans
    ((σ.subtypeEquiv (fun x => by simp only [ne_eq, σ.injective.eq_iff])).trans
      (finSuccAboveEquiv (σ j)).symm)

/-- 概要：置換の削除は残りの位置の succAbove と可換する（Berger–Fresse §1.1.3）。
方針：一点を除いた出力の昇順同値とその逆写像を消去する。
規約：削除する出力は σ(j) である。
使われ方：置換の削除と挿入が互いに逆であることを示す。 -/
@[simp] lemma deletePermutation_succAbove {N : ℕ} (σ : Equiv.Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (x : Fin N) :
    (σ j).succAbove (deletePermutation σ j x) = σ (j.succAbove x) := by
  change ((finSuccAboveEquiv (σ j))
    ((finSuccAboveEquiv (σ j)).symm ⟨σ (j.succAbove x), _⟩)).val = _
  exact congrArg Subtype.val ((finSuccAboveEquiv (σ j)).apply_symm_apply _)

/-- 概要：置換から一つの対応を削除して挿入し直すと元に戻る（Berger–Fresse §1.1.3）。
方針：挿入位置とそれ以外の succAbove の像に分けて計算する。
規約：入力位置 j と出力 σ(j) を同時に戻す。
使われ方：削除前後の signature の比較を正当化する。 -/
@[simp] lemma insertPermutation_deletePermutation {N : ℕ}
    (σ : Equiv.Perm (Fin (N + 1))) (j : Fin (N + 1)) :
    insertPermutation j (σ j) (deletePermutation σ j) = σ := by
  apply Equiv.ext
  intro x
  by_cases hx : x = j
  · subst x
    exact insertPermutation_at _ _ _
  · obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [insertPermutation_succAbove, deletePermutation_succAbove]

/-- 概要：一つの対応の挿入による signature の変化（Berger–Fresse §1.1.3）。
方針：二つの巡回置換の signature と先頭への置換の拡張の signature を掛ける。
規約：符号は入力位置と出力位置の番号の和の偶奇で決まる。
使われ方：shuffle 境界の符号を削除後の shuffle の符号と比較する。 -/
lemma sign_insertPermutation {N : ℕ} (j a : Fin (N + 1)) (σ : Equiv.Perm (Fin N)) :
    Equiv.Perm.sign (insertPermutation j a σ) =
      (-1 : ℤˣ) ^ (a.val + j.val) * Equiv.Perm.sign σ := by
  simp only [insertPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm,
    Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul, pow_add]
  ac_rfl

/-- 概要：削除した置換の signature と元の signature の関係（Berger–Fresse §1.1.3）。
方針：削除・挿入の逆性を挿入の signature の公式へ適用する。
規約：削除位置は j、削除した像の位置は σ(j)。
使われ方：各同方向の境界面の符号を求める。 -/
lemma sign_deletePermutation {N : ℕ} (σ : Equiv.Perm (Fin (N + 1))) (j : Fin (N + 1)) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ ((σ j).val + j.val) * Equiv.Perm.sign (deletePermutation σ j) := by
  simpa only [insertPermutation_deletePermutation] using
    sign_insertPermutation j (σ j) (deletePermutation σ j)

end SerrePositivity.EInfinity.BarrattEccles
