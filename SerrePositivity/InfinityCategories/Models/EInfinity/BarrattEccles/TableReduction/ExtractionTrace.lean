module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows
public import Mathlib.Data.List.Nodup

/-!
模型。文献の定義との比較は後で
# 成功した table の行ごとの抽出の証跡

概要：Berger–Fresse §1.4.4 の境界比較で使う各行の抽出結果と除外状態を保持する。
方針：reduceRows の成功分岐と同じデータを帰納的な命題にまとめる。
規約：証跡の連結は既存の reduceRows と厳密に一致する。
使われ方：各行末と再出現位置、削除位置と符号の対応を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：table の各行で選んだ語と後続の除外状態の証跡（BF §1.4.4）。
方針：長さの成功条件と次の行の証跡を一段ずつ記録する。
規約：選択語は元の reduceRows と同じ take で定める。
使われ方：平坦な出力から行の分割とその不変条件を取り出す。 -/
inductive ExtractionTrace : List (List α × ℕ) → List α → List (List α) → Prop
  | nil (removed : List α) : ExtractionTrace [] removed []
  | cons {row : List α} {r : ℕ} {rest : List (List α × ℕ)}
      {removed : List α} {picked : List (List α)}
      (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
      (tail : ExtractionTrace rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) picked) :
      ExtractionTrace ((row, r) :: rest) removed ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r :: picked)

namespace ExtractionTrace

/-- 概要：証跡の選択行を連結すると既存の抽出結果（BF §1.4.4）。
方針：帰納法で各行の成功を再構成する。
規約：新しい抽出アルゴリズムを仮定しない。
使われ方：行ごとの証明を実際の TR の出力へ渡す。 -/
lemma reduceRows {rows : List (List α × ℕ)} {removed : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some picked.flatten := by
  induction h with
  | nil => rfl
  | cons hr hb ht ih =>
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success _ _ _ _ _ hr hb ih

/-- 概要：各選択行の長さは指定された行長（BF §1.3.1）。
方針：take の長さの成功条件と後続の帰納法を使う。
規約：順序付きのリストの等式。
使われ方：行の境界の位置と行数を確定する。 -/
lemma lengths {rows : List (List α × ℕ)} {removed : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) :
    picked.map List.length = rows.map Prod.snd := by
  induction h with
  | nil => rfl
  | cons hr hb ht ih =>
    simp only [List.map_cons, List.length_take, Nat.min_eq_left hb, ih]

/-- 概要：選択した行数は元の行数と同じ（BF §1.3.1）。
方針：行長リストの等式の長さを取る。
規約：失敗した抽出は証跡を持たない。
使われ方：非最終行末の候補の個数を計算する。 -/
lemma length {rows : List (List α × ℕ)} {removed : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) : picked.length = rows.length := by
  simpa only [List.length_map] using congrArg List.length h.lengths

/-- 概要：各選択行は空でない（BF §1.3.1）。
方針：行長の正値性と take の長さを使う。
規約：空の table の条件は空。
使われ方：各行の末尾を一つずつ数える。 -/
lemma nonempty {rows : List (List α × ℕ)} {removed : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) : ∀ row ∈ picked, row ≠ [] := by
  induction h with
  | nil => simp
  | cons hr hb ht ih =>
    intro row hm
    rcases List.mem_cons.mp hm with rfl | hm
    · intro he
      have hl := congrArg List.length he
      simp only [List.length_take, Nat.min_eq_left hb, List.length_nil] at hl
      omega
    · exact ih _ hm

/-- 概要：既に除外した値は後続の出力に現れない（BF §1.3.1）。
方針：現在行は filter で除外し、次の除外リストは現在のリストを含む。
規約：元の行の重複の有無によらない。
使われ方：行の末尾以外の文字が最終出現であることを示す。 -/
lemma removed_not_mem_output {rows : List (List α × ℕ)} {removed : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked)
    (a : α) (ha : a ∈ removed) : a ∉ picked.flatten := by
  induction h generalizing a with
  | nil => simp
  | cons hr hb ht ih =>
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · have hav := List.mem_of_mem_take hm
      have hn : a ∉ _ := (List.mem_filter.mp hav).2 |> of_decide_eq_true
      exact hn ha
    · exact ih a (List.mem_append_left _ ha) hm

end ExtractionTrace

/-- 概要：抽出成功から行ごとの証跡を取り出す（BF §1.4.4）。
方針：既存の一行の成功条件を取り出し、後続で帰納する。
規約：平坦な出力との等式も同時に得る。
使われ方：既存の TR の各成功項に行ごとの不変条件を適用する。 -/
lemma extractionTrace_of_reduceRows (rows : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some out) :
    ∃ picked, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked ∧ picked.flatten = out := by
  induction rows generalizing removed out with
  | nil =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at h
    subst out
    exact ⟨[], .nil removed, rfl⟩
  | cons p rows ih =>
    obtain ⟨hr, hb, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨picked, hp, hflat⟩ := ih _ _ ht
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 :: picked, .cons hr hb hp, ?_⟩
    simpa only [List.flatten_cons, hflat] using he.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
