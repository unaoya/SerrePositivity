module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWordOccurrence

/-!
模型。文献の定義との比較は後で
# 水平成分語と外側語の出現間の代入

概要：Berger–Fresse §1.5.7 の水平語の指定値以外の部分を元のリスト代入へ同定する。
方針：指定値のない語への代入は水平ラベルの写像であることを使う。
規約：内側の固定文字は境界の実際の文字。
使われ方：blockWord の水平部分を compositeWord の出現間の部分へ照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値を含まない語への代入は水平ラベルの写像（BF §1.5.7）。
方針：元の語で帰納し、指定値以外の分岐だけを使う。
規約：内側部分語列の個数は任意。
使われ方：出現境界間の水平文字を実際の代入へ移す。 -/
lemma substitute_horizontal_no_slot {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (hk : k ∉ xs) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts = xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a ≠ k := fun he => hk (by simp [he])
    have ht : k ∉ xs := fun hm => hk (List.mem_cons_of_mem a hm)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, ih ht, List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel, dite_eq_right ha]

namespace TableCompositionData

/-- 概要：最初の水平語の末尾を省いた部分は最初の出現以前の代入語（BF §1.5.7）。
方針：水平閉区間の最後の指定値を除き、それ以前の不出現を使う。
規約：最初の出現が先頭なら両辺は空語。
使われ方：融合出力と compositeWord の最初の成分を接続する。 -/
lemma firstHorizontal_dropLast {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    (c.horizontalWord 0).dropLast =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
        ((List.ofFn c.outerWord.val).take
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos c.outerWord c.slot⟩).val)
        (c.cuts.segments c.innerWord.val) := by
  let j : Fin c.count := ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos c.outerWord c.slot⟩
  have hk : c.slot ∉ (List.ofFn c.outerWord.val).take
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val := by
    have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice c.outerWord.val c.slot 0
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val (fun p _ hp =>
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_before_first c.outerWord.val c.slot j.isLt p hp)
    simpa only [List.drop_zero, Nat.sub_zero] using hn
  have hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot 1 =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_at c.outerWord.val c.slot j
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1 ≤
      (List.ofFn c.outerWord.val).length := by
    rw [List.length_ofFn]
    have := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).isLt
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_horizontal_no_slot c.slot (c.innerWord.val (c.innerPosition 0)) _ _ hk]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_zero, Nat.zero_add,
    hb, List.drop_zero, Nat.sub_zero]
  rw [← List.map_dropLast, List.dropLast_take hp, Nat.add_sub_cancel]

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
