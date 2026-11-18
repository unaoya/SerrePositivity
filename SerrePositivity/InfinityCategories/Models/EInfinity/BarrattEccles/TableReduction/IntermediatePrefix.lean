module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 全中間行を通した早い除外の輸送

概要：Berger–Fresse §1.4.4 の直前出現から削除行まで同じ値を早く除外する。
方針：先行抽出の証跡で帰納し、選択部分の不変性と除外所属の同値を保持する。
規約：中間行の出力に削除値がないことを要求する。
使われ方：受け取り行の後を短くした削除行の局所計算につなぐ。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ一文字を早く除外しても全中間行の選択を保つ（BF §1.4.4）。
方針：元の状態の所属に一文字を足した関係を各段で帰納する。
規約：終端の除外はリストの等式ではなく所属の同値で指定する。
使われ方：任意個の中間行を通して、削除値の早い除外を運ぶ。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.early_exclusion {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) (a : α) :
    a ∉ picked.flatten → ∀ other : List α, (∀ x, x ∈ other ↔ x ∈ removed ∨ x = a) →
      ∃ newFinish, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before other picked newFinish ∧
        ∀ x, x ∈ newFinish ↔ x ∈ finish ∨ x = a := by
  induction h with
  | nil removed =>
    intro _ other hm
    exact ⟨other, .nil other, hm⟩
  | @cons row r rest removed picked finish hr hb ht ih =>
    intro ha other hm
    have hhead : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r := by
      intro hx
      exact ha (List.mem_append_left _ hx)
    have htail : a ∉ picked.flatten := by
      intro hx
      exact ha (List.mem_append_right _ hx)
    have hother : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row := by
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_congr_removed
      intro x
      simpa only [List.mem_append, List.mem_singleton] using hm x
    have hselected : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row).take r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r := by
      rw [hother, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.intermediate_selected_eq removed row a r hhead]
    have hexcluded : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row).take (r - 1) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by
      rw [hother, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.intermediate_excluded_eq removed row a r hhead]
    have hbound : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row).length := by
      have hlen := congrArg List.length hselected
      simp only [List.length_take, Nat.min_eq_left hb] at hlen
      omega
    have hnext : ∀ x, x ∈ other ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row).take (r - 1) ↔
        x ∈ removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ∨ x = a := by
      intro x
      simp only [List.mem_append, hexcluded, hm x]
      tauto
    obtain ⟨newFinish, hnew, hfinish⟩ := ih htail _ hnext
    have hprefix := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.cons hr hbound hnew
    rw [hselected] at hprefix
    exact ⟨newFinish, hprefix, hfinish⟩

/-- 概要：早い除外を全中間行に通して変更後の後続抽出へつなぐ（BF §1.4.4）。
方針：終端状態の所属を合わせ、既存抽出の一致と先行証跡の連結を使う。
規約：後続行は変更後の行リストでよい。
使われ方：短くした削除行を受け取り行後の実際の抽出へ接続する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.append_early_exclusion {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) (a : α) (ha : a ∉ picked.flatten)
    (rest : List (List α × ℕ)) (out : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (finish ++ [a]) = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) (removed ++ [a]) = some (picked.flatten ++ out) := by
  obtain ⟨newFinish, hnew, hm⟩ := h.early_exclusion a ha (removed ++ [a])
    (by intro x; simp only [List.mem_append, List.mem_singleton])
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest newFinish (finish ++ [a]) (by
    intro x
    simpa only [List.mem_append, List.mem_singleton] using hm x)
  exact hnew.append rest out (he.trans ht)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
