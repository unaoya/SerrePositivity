module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.FirstOccurrences

/-!
模型。文献の定義との比較は後で
# 最初の出現の選択の一文字の変化

概要：Berger–Fresse §1.4.2–3 の隣接する復元行を比較するためのリストの式。
方針：末尾への文字追加と最終重複除去を比較し、反転して先頭の選択の式を得る。
規約：同じ値は一度だけ残し、残りの値の相対順序は保つ。
使われ方：復元行で一つの文字を前後へ移す規則を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α : Type*} [DecidableEq α]

/-- 概要：末尾へ加えた文字の以前の出現を除く式（BF §1.4.2）。
方針：語の先頭で帰納し、追加した値との一致と尾部への所属で分岐する。
規約：dedup は最終出現を残す。
使われ方：最初の出現を残す処理の先頭の式へ反転する。 -/
lemma dedup_append_singleton (xs : List α) (a : α) :
    (xs ++ [a]).dedup = xs.dedup.filter (fun x => x ≠ a) ++ [a] := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases hba : b = a
    · subst b
      by_cases ha : a ∈ xs <;> simpa [List.dedup_cons, ha] using ih
    · by_cases hb : b ∈ xs
      · simpa [List.dedup_cons, hba, hb] using ih
      · simpa [List.dedup_cons, hba, hb] using congrArg (b :: ·) ih

/-- 概要：先頭の値を残し、後続の同値を全て除く式（BF §1.4.2）。
方針：最終重複除去の末尾追加の式を反転する。
規約：残りの値の順序は保たれる。
使われ方：区切りを通過したときの一文字の移動を明示する。 -/
lemma firstOccurrences_cons (a : α) (xs : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (a :: xs) = a :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs).filter (fun x => x ≠ a) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences, List.reverse_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.dedup_append_singleton,
    List.reverse_append, List.reverse_nil, List.nil_append, List.singleton_append,
    ← List.filter_reverse]

/-- 概要：後続に現れない先頭の値はそのまま残る（BF §1.4.2）。
方針：選択後の語にも同値がないので filter が恒等になる。
規約：空の後続語も含む。
使われ方：最終出現を通過したときの復元行の不変性を示す。 -/
lemma firstOccurrences_cons_of_not_mem (a : α) (xs : List α) (ha : a ∉ xs) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (a :: xs) = a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences xs := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons]
  congr 1
  apply List.filter_eq_self.mpr
  intro b hb
  have hb' : b ∈ xs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_firstOccurrences b xs).mp hb
  have hba : b ≠ a := fun h => ha (h ▸ hb')
  simpa only [decide_eq_true_eq] using hba

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
