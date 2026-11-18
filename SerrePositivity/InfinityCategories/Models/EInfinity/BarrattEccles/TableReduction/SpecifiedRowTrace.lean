module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace

/-!
模型。文献の定義との比較は後で
# 指定した行分割を持つ実際の抽出証跡

概要：Berger–Fresse §1.5.8 の外側復元で、行ごとに指定した選択語を成功証跡へ戻す。
方針：平坦な出力と行長が一致すれば、リストの行分割は一意である。
規約：行長は元の表の行長と同じ順序で比較する。
使われ方：復元外側語の境界情報を実際の圧縮前の抽出証跡へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：成功出力と各行長が合う指定選択語は実際の抽出証跡を持つ（BF §1.5.8）。
方針：成功から証跡を取り出し、平坦化と行長の一致で選択語列を一意に決める。
規約：指定選択語の非退化性や非空性を別に要求しない。
使われ方：外側行の復元語を証跡の選択行として固定する。 -/
lemma extractionTrace_of_lengths (rows : List (List α × ℕ)) (removed : List α)
    (picked : List (List α)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some picked.flatten)
    (hl : picked.map List.length = rows.map Prod.snd) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked := by
  obtain ⟨picked', ht, hf⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows rows removed picked.flatten h
  have he : picked' = picked := List.eq_iff_flatten_eq.mpr ⟨hf, ht.lengths.trans hl.symm⟩
  exact he ▸ ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
