module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Nodup

/-!
模型。文献の定義との比較は後で
# 最初の出現の順序による値の列挙

概要：Berger–Fresse §1.4.2 の復元する置換の残りを、最初の出現の順に並べる。
方針：反転したリストから最後の重複を除き、再び反転する。
規約：元の語に現れる値をちょうど一度ずつ残す。
使われ方：各 table の行の開始位置から見た残りの値の順序を指定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- 概要：値を最初の出現の順に一度ずつ残す（BF §1.4.2）。
方針：逆順での最終出現の選択を使う。
規約：dedup 自体は最後の出現を残すので二度反転する。
使われ方：復元する置換の後半を構成する。 -/
def firstOccurrences (xs : List α) : List α := xs.reverse.dedup.reverse

/-- 概要：最初の出現の選択は値の集合を保つ（BF §1.4.2）。
方針：反転と重複除去の所属判定を使う。
規約：位置の番号による条件を要求しない。
使われ方：復元する置換の全射性を示す。 -/
@[simp] lemma mem_firstOccurrences (a : α) (xs : List α) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs ↔ a ∈ xs := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences]

/-- 概要：最初の出現だけを残した語は重複しない（BF §1.4.2）。
方針：dedup の重複のないことと反転の保存を使う。
規約：元の語に重複があってよい。
使われ方：復元する置換の単射性を示す。 -/
lemma firstOccurrences_nodup (xs : List α) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs).Nodup := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences, List.nodup_reverse] using List.nodup_dedup xs.reverse

/-- 概要：重複のない語は最初の出現の選択で変わらない（BF §1.4.2）。
方針：反転も重複しないので dedup が恒等になる。
規約：空語を含む。
使われ方：次数零で復元の式を簡約する。 -/
lemma firstOccurrences_eq_self (xs : List α) (hx : xs.Nodup) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs = xs := by
  have hr : xs.reverse.Nodup := by simpa only [List.nodup_reverse] using hx
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences, hr.dedup, List.reverse_reverse]

/-- 概要：単射な値の変更は最初の出現の選択と可換（BF §1.4.2）。
方針：反転と単射な写像による重複除去の自然性を使う。
規約：位置の順序を保つ。
使われ方：復元される置換列の値の置換との両立を検証する。 -/
lemma firstOccurrences_map (f : α → β) (hf : Function.Injective f) (xs : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (xs.map f) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs).map f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences, ← List.map_reverse, List.dedup_map_of_injective hf]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
