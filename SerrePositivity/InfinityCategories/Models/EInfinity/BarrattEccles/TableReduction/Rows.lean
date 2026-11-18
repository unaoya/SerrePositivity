module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.TakeDrop

/-!
模型。文献の定義との比較は後で
# Table reduction の行の抽出

概要：Berger–Fresse §1.3.1 の先行行による文字の除外を有限リストで実装する。
方針：残った文字の先頭を取り、末尾以外を以後の除外リストへ加える。
規約：各行は正の長さとし、文字が不足する選択は none とする。
使われ方：一般の TR の各行長の選択に対する出力を計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- 概要：先行行で確定した最終出現の文字を除く（BF §1.3.1）。
方針：除外リストに属さない文字だけを元の順に残す。
規約：除外リストには先行行の末尾を加えない。
使われ方：各置換の行から使用できる文字を取り出す。 -/
def available (removed row : List α) : List α := row.filter (fun x => x ∉ removed)

/-- 概要：table の全行を順に抽出して連結する（BF §1.3.1）。
方針：行長を検査し、先頭の指定文字と再帰的な残りを連結する。
規約：空の行または文字の不足は無効な行長の選択として捨てる。
使われ方：TR の有限和の一項となる語を計算する。 -/
def reduceRows : List (List α × ℕ) → List α → Option (List α)
  | [], _ => some []
  | (row, r) :: rows, removed =>
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row
    if 0 < r ∧ r ≤ xs.length then
      (reduceRows rows (removed ++ xs.take (r - 1))).map (xs.take r ++ ·)
    else none

/-- 概要：行がなければ空語を返す（BF §1.3.1）。
方針：再帰の初期値を評価する。
規約：除外された文字の集合によらない。
使われ方：最終行の式を簡約する。 -/
@[simp] lemma reduceRows_nil (removed : List α) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [] removed = some [] := rfl

/-- 概要：抽出に成功した語の長さは指定した行長の和（BF §1.3.1）。
方針：行数で帰納し、take の長さと後続行の長さを足す。
規約：不可能な行長の選択は仮定から排除される。
使われ方：出力を長さ n+d の全射語の候補へ移す。 -/
lemma reduceRows_length (rows : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some out) :
    out.length = (rows.map Prod.snd).sum := by
  induction rows generalizing removed out with
  | nil =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at h
    subst out
    rfl
  | cons row rows ih =>
    rcases row with ⟨row, r⟩
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows] at h
    split at h
    · rename_i hr
      cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) with
      | none => simp [he] at h
      | some tail =>
        simp only [he, Option.map_some, Option.some.injEq] at h
        subst out
        simp only [List.length_append, List.length_take, Nat.min_eq_left hr.2,
          ih _ _ he, List.map_cons, List.sum_cons]
    · simp at h

/-- 概要：単射な文字の変更は除外処理と可換（BF §1.3.6）。
方針：所属判定の保存を使い、リストを先頭から比較する。
規約：文字の位置と行の長さは変えない。
使われ方：TR の置換同変性の各行の比較となる。 -/
lemma available_map (f : α → β) (hf : Function.Injective f)
    (removed row : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.map f) (row.map f) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).map f := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_cons, List.map_cons] at *
    have hm : f a ∈ removed.map f ↔ a ∈ removed := List.mem_map_of_injective hf
    simp only [hm]
    split <;> simp_all

/-- 概要：単射な文字の変更は table の全行の抽出と可換（BF §1.3.6）。
方針：各行の filter・take と再帰の除外リストを同時に比較する。
規約：失敗する行長の選択も保存する。
使われ方：一般の TR の同変性を項ごとに証明する。 -/
lemma reduceRows_map (f : α → β) (hf : Function.Injective f)
    (rows : List (List α × ℕ)) (removed : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (rows.map (fun p => (p.1.map f, p.2))) (removed.map f) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed).map (List.map f) := by
  induction rows generalizing removed with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨row, r⟩
    simp only [List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_map f hf, List.length_map]
    split
    · simp only [← List.map_take]
      rw [← List.map_append, ih]
      simp only [Option.map_map, Function.comp_def, List.map_append]
    · rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
