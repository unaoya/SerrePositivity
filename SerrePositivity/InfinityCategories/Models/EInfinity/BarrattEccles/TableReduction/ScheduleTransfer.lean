module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence

/-!
模型。文献の定義との比較は後で
# 削除項の相殺相手の行長の移動

概要：Berger–Fresse §1.4.4 の r_j+1・r_i−1 という行長変更を有限関数で構成する。
方針：異なる二位置の更新として定義し、正値性・上界・総和と逆の移動を証明する。
規約：減らす行は長さ 2 以上、増やす行には arity の余裕を要求する。
使われ方：最終出現の削除と区切りの削除の相殺対の Schedule を指定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：一つの行から別の行へ長さを 1 移す（BF §1.4.4）。
方針：減らす行を更新してから増やす行を更新する。
規約：自然数の差で定義し、使用時に減らす行の正値性を供給する。
使われ方：相殺相手の行長の関数を作る。 -/
def transferUnit {m : ℕ} (r : Fin m → ℕ) (donor receiver : Fin m) : Fin m → ℕ :=
  Function.update (Function.update r donor (r donor - 1)) receiver (r receiver + 1)

/-- 概要：増やす行の新しい長さ（BF §1.4.4）。
方針：最後の更新を評価する。
規約：増分は 1。
使われ方：相殺相手の行長の成分を計算する。 -/
@[simp] lemma transferUnit_receiver {m : ℕ} (r : Fin m → ℕ) (i j : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j j = r j + 1 := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit]

/-- 概要：減らす行の新しい長さ（BF §1.4.4）。
方針：二行が異なるため二度目の更新は影響しない。
規約：減分は 1。
使われ方：正値性と逆の移動を検証する。 -/
@[simp] lemma transferUnit_donor {m : ℕ} (r : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j i = r i - 1 := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit, hij]

/-- 概要：他の全ての行の長さは変わらない（BF §1.4.4）。
方針：二つの更新のどちらの位置でもないことを使う。
規約：k は減らす行とも増やす行とも異なる。
使われ方：相殺相手の table が二行以外を変えないことを示す。 -/
lemma transferUnit_other {m : ℕ} (r : Fin m → ℕ) (i j k : Fin m)
    (hki : k ≠ i) (hkj : k ≠ j) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j k = r k := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit, hki, hkj]

/-- 概要：長さを一つ移しても総和は不変（BF §1.4.4）。
方針：各成分に足し戻す 1 の指示関数を使って全成分を加算する。
規約：減らす行の長さは 1 以上。
使われ方：相殺相手も同じ次数の Schedule となる。 -/
lemma transferUnit_sum {m : ℕ} (r : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hi : 0 < r i) : (∑ k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j k) = ∑ k, r k := by
  have hs : (∑ k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j k) + (∑ k : Fin m, if k = i then 1 else 0) =
      (∑ k, r k) + (∑ k : Fin m, if k = j then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor r i j hij]
      simp only [↓reduceIte, hij]
      omega
    · by_cases hkj : k = j
      · subst k
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver]
        simp only [↓reduceIte, hki]
      · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other r i j k hki hkj]
        simp only [hki, hkj, ↓reduceIte, Nat.add_zero]
  simpa using hs

/-- 概要：逆向きに長さを移すと元の関数に戻る（BF §1.4.4）。
方針：二つの更新位置とそれ以外を成分ごとに比較する。
規約：最初に減らす行は正の長さ。
使われ方：相殺対の対応が逆を持つことの算術的な部分を与える。 -/
lemma transferUnit_inverse {m : ℕ} (r : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hi : 0 < r i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j) j i = r := by
  funext k
  by_cases hki : k = i
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor r i j hij]
    omega
  · by_cases hkj : k = j
    · subst k
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor _ j i hij.symm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver]
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other _ j i k hkj hki, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other r i j k hki hkj]

/-- 概要：長さ 2 以上の行から移すと全行長の正値性を保つ（BF §1.4.4）。
方針：更新した二行と残りの行で分岐する。
規約：入力の全行長は正。
使われ方：相殺相手の Schedule の正値条件を供給する。 -/
lemma transferUnit_pos {m : ℕ} (r : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hr : ∀ k, 0 < r k) (hi : 1 < r i) (k : Fin m) : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j k := by
  by_cases hki : k = i
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor r i j hij]
    omega
  · by_cases hkj : k = j
    · subst k
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver]
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other r i j k hki hkj]
      exact hr k

/-- 概要：増やす行に余裕があれば arity の上界を保つ（BF §1.4.4）。
方針：増やす行だけは厳密な上界を使い、他の行は既存の上界を使う。
規約：行長は n 以下。
使われ方：相殺相手の有限な行長の型を構成する。 -/
lemma transferUnit_le {m n : ℕ} (r : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hr : ∀ k, r k ≤ n) (hj : r j < n) (k : Fin m) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit r i j k ≤ n := by
  by_cases hki : k = i
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor r i j hij]
    have hb := hr i
    omega
  · by_cases hkj : k = j
    · subst k
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver]
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other r i j k hki hkj]
      exact hr k

/-- 概要：行長を一つ移して作る同じ次数の Schedule（BF §1.4.4）。
方針：自然数の行長の移動を有限添字に入れ、正値性と総和を束ねる。
規約：二行の相違・減らす行の余裕・増やす行の余裕を引数に取る。
使われ方：削除項の相殺相手の候補となる実際の Schedule。 -/
def scheduleTransfer {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i j : Fin (d + 1)) (hij : i ≠ j)
    (hi : 1 < (r.val i).val) (hj : (r.val j).val < n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d :=
  ⟨fun k => ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit (fun k => (r.val k).val) i j k,
      Nat.lt_succ_of_le (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_le _ i j hij
        (fun k => Nat.le_of_lt_succ (r.val k).isLt) hj k)⟩,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_pos _ i j hij r.property.1 hi,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_sum _ i j hij (by omega)).trans r.property.2⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
