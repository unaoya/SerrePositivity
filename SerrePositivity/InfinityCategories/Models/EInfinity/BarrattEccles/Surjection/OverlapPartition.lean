module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Words
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.OfFn

/-!
模型。文献の定義との比較は後で
# 部分合成の端点を重ねた分割

概要：Berger–Fresse §1.2.4 の内側語を出現回数だけ分ける有限な添字を構成する。
方針：各部分語の長さを持ち、重なる端点の個数を総長の条件に組み込む。
規約：内側が空の場合も許し、各部分語は空となる。
使われ方：χ の部分合成の実際の有限和の添字となる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：長さ l の語を t 個の端点を重ねた部分語へ分ける添字（BF §1.2.4）。
方針：部分長は l 以下、非空語では正、部分長総和＋1＝l＋t とする。
規約：l＝0 の場合は t＝1 のときだけ空の分割が存在する。
使われ方：空入力の挿入も含む合成の添字を有限型として与える。 -/
abbrev OverlapPartition (t l : ℕ) :=
  {r : Fin t → Fin (l + 1) // (∀ i, 0 < (r i).val ∨ l = 0) ∧
    (∑ i, (r i).val) + 1 = l + t}

namespace OverlapPartition

variable {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)

/-- 概要：非空語の各部分長は正（BF §1.2.4）。
方針：分割の条件から空語の分岐を排除する。
規約：部分語の個数が零でも成り立つ。
使われ方：端点を共有する区間の範囲を計算する。 -/
lemma positive (hl : 0 < l) (i : Fin t) : 0 < (r.val i).val := by
  rcases r.property.1 i with h | h
  · exact h
  · omega

/-- 概要：端点を重ねた分割の各部分長の総和（BF §1.2.4）。
方針：定義の加法等式を減算の形へ直す。
規約：空語の唯一の空部分語も含む。
使われ方：合成語の長さを入力次数から計算する。 -/
lemma sum_lengths : (∑ i, (r.val i).val) = l + t - 1 := by
  have := r.property.2
  omega

/-- 概要：空の内側語を分割できるのは一部分の場合だけ（BF §1.2.4 の空語拡張）。
方針：全ての有限な部分長が零であることを総和条件へ代入する。
規約：この場合、指定値の複数出現への空語代入の和は空となる。
使われ方：nullary の部分合成を零 arity の基底と整合させる。 -/
lemma count_eq_one_of_empty (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t 0) : t = 1 := by
  have hz : (∑ i, (r.val i).val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have := (r.val i).isLt
    omega
  have := r.property.2
  omega

/-- 概要：部分語の開始位置はそれ以前の部分長−1 の総和（BF §1.2.4）。
方針：一つ前の部分語の末尾を次の先頭として使う。
規約：零始まり、空語の場合の開始位置も零。
使われ方：内側語の drop と take で各部分語を切り出す。 -/
def start (i : Fin t) : ℕ :=
  ((List.ofFn (fun j => (r.val j).val - 1)).take i.val).sum

/-- 概要：分割の最初の開始位置は零（BF §1.2.4）。
方針：先行部分が空であることを使う。
規約：最初の添字が存在する場合。
使われ方：分割が内側語の先頭から始まることを照合する。 -/
@[simp] lemma start_zero (ht : 0 < t) : r.start ⟨0, ht⟩ = 0 := rfl

/-- 概要：非空語では各部分長−1 の総和＋1 が元の語長（BF §1.2.4）。
方針：各正の部分長から引いた 1 を足し戻し、総和条件を使う。
規約：部分語の個数には追加仮定なし。
使われ方：最後の部分語の終了位置と範囲を計算する。 -/
lemma sum_steps (hl : 0 < l) : (∑ i, ((r.val i).val - 1)) + 1 = l := by
  have hs : (∑ i, (r.val i).val) = (∑ i, ((r.val i).val - 1)) + t := by
    calc
      _ = ∑ i, (((r.val i).val - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have := r.positive hl i
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have := r.property.2
  omega

end OverlapPartition

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
