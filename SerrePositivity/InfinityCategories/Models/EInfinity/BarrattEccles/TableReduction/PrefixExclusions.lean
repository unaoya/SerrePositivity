module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows

/-!
模型。文献の定義との比較は後で
# 先行抽出後の除外状態の長さと重複のなさ

概要：Berger–Fresse §1.4.4 の逆対応で利用可能な値の個数を計数する。
方針：各行で長さ−1 の文字を加え、既に除外した値を再び加えないことを使う。
規約：元の各行は重複を持たない。
使われ方：最後の行で利用可能な値を取り尽くすことと、除外を解いた値の再出現を導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：先行抽出後の除外長は各行の長さ−1 の総和を加えたもの（BF §1.4.4）。
方針：take の長さの成功条件を各段で評価する。
規約：除外リストの実際の長さの等式。
使われ方：利用可能行の長さの余裕と最後の行の飽和を計算する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.finish_length {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) :
    finish.length = removed.length + (before.map (fun p => p.2 - 1)).sum := by
  induction h with
  | nil => simp
  | cons hr hb ht ih =>
    have hle : _ ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available _ _).length := Nat.le_trans (Nat.sub_le _ 1) hb
    simp only [List.length_append, List.length_take, Nat.min_eq_left hle] at ih
    simp only [List.map_cons, List.sum_cons]
    omega

/-- 概要：重複のない行の先行抽出は除外状態の重複のなさを保つ（BF §1.4.4）。
方針：新しく加える選択部分は重複せず、元の除外に属さないことを使う。
規約：初期除外も重複を持たない。
使われ方：除外長を実際に除いた値の個数として使う。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.finish_nodup {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) : removed.Nodup →
      (∀ p ∈ before, p.1.Nodup) → finish.Nodup := by
  induction h with
  | nil => intro hn _; exact hn
  | @cons row r rest removed picked finish hr hb ht ih =>
    intro hn hrows
    apply ih
    · apply List.nodup_append.mpr
      refine ⟨hn, ((hrows (row, r) (by simp)).filter _).take, ?_⟩
      intro x hx y hy hxy
      have hy' : y ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row := List.mem_of_mem_take hy
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, decide_eq_true_eq] at hy'
      exact hy'.2 (hxy ▸ hx)
    · intro p hp
      exact hrows p (List.mem_cons_of_mem _ hp)

/-- 概要：二つの先行抽出の証跡を終端状態で連結する（BF §1.4.4）。
方針：前の証跡の行で帰納する。
規約：選択行の順序と最後の除外状態を保持する。
使われ方：受け取り行以前と中間行を最終行直前までの一つの証跡へまとめる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.trans {before rest : List (List α × ℕ)}
    {removed middle finish : List α} {picked selected : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked middle)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rest middle selected finish) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (before ++ rest) removed (picked ++ selected) finish := by
  induction h with
  | nil => simpa only [List.nil_append] using ht
  | cons hr hb htail ih =>
    exact .cons hr hb (ih ht)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
