module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence
public import Mathlib.Data.List.FinRange

/-!
模型。文献の定義との比較は後で
# 抽出した行の内部の文字は後続行に現れない

概要：Berger–Fresse §1.4.4 の table の区切り候補が行末だけであることの不変条件。
方針：行は重複せず、末尾以外は以後の除外リストに含まれることを証跡で示す。
規約：行末は除外しない。
使われ方：出力の区切りと行末の対応を計数で確定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：各行は重複せず、末尾以外は後続に現れない（BF §1.4.4）。
方針：先頭行の不変条件と後続の同じ条件を再帰的に束ねる。
規約：空の table にも適用する。
使われ方：行ごとの最終出現と再出現の区別を扱う。 -/
def SeparatedRows : List (List α) → Prop
  | [] => True
  | row :: rest => row.Nodup ∧ (∀ a ∈ row.dropLast, a ∉ rest.flatten) ∧ SeparatedRows rest

/-- 概要：長さ r の選択行の末尾以外は take(r−1)（BF §1.3.1）。
方針：dropLast の長さの式と take の合成を使う。
規約：選択可能な長さ r 以下で主張する。
使われ方：実際の次の除外リストへ行内部の文字を渡す。 -/
lemma dropLast_take_of_le_length {β : Type*} (xs : List β) (r : ℕ) (hr : r ≤ xs.length) :
    (xs.take r).dropLast = xs.take (r - 1) := by
  rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left hr, List.take_take,
    Nat.min_eq_left (Nat.sub_le r 1)]

/-- 概要：重複しない元の行の抽出証跡は行の分離条件を満たす（BF §1.4.4）。
方針：末尾以外の文字は次の除外リストに属し、後続の出力から除かれる。
規約：元の行の全射性は要求しない。
使われ方：全ての成功した TR 項に不変条件を適用する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.separatedRows {rows : List (List α × ℕ)} {removed : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked) :
    (∀ p ∈ rows, p.1.Nodup) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked := by
  induction h with
  | nil => intro _; trivial
  | @cons row r rest removed picked hr hb ht ih =>
    intro hn
    refine ⟨((hn (row, r) (by simp)).filter _).take, ?_, ?_⟩
    · intro a ha
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dropLast_take_of_le_length _ _ hb] at ha
      exact ht.removed_not_mem_output a (List.mem_append_right _ ha)
    · exact ih (fun p hp => hn p (List.mem_cons_of_mem _ hp))

/-- 概要：TR の元の置換の行は全て重複しない（BF §1.3.1）。
方針：逆置換の単射性を ofFn の重複のなさへ移す。
規約：任意の Schedule に適用する。
使われ方：抽出証跡の行の分離条件の入力を供給する。 -/
lemma rows_nodup {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) : ∀ p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r, p.1.Nodup := by
  intro p hp
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact List.nodup_ofFn_ofInjective (w i).symm.injective

/-- 概要：成功した TR の出力を分離した非空の各行へ分割する（BF §1.4.4）。
方針：抽出証跡を取り、元の置換の行の重複のなさを適用する。
規約：出力自体は退化していてもよい。
使われ方：行末が全ての区切り候補であることを証明する。 -/
lemma separatedRows_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ picked, picked.flatten = out ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked ∧
      (∀ row ∈ picked, row ≠ []) ∧ picked.length = d + 1 ∧
        picked.map List.length = List.ofFn (fun i => (r.val i).val) := by
  obtain ⟨picked, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ _ _ h
  refine ⟨picked, he, hp.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w r), hp.nonempty, ?_, ?_⟩
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using hp.length
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def] using hp.lengths

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
