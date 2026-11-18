module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntermediateStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 抽出の先行部分とその終端の除外状態

概要：Berger–Fresse §1.4.4 の受け取り行・中間行・削除行をつなぐ証跡を与える。
方針：既存 reduceRows と同じ一段の条件を使い、選択行と終端状態を保持する。
規約：新しい抽出アルゴリズムではなく、元の再帰の有限な先行部分を記述する命題。
使われ方：中間行を通した早い除外と後続抽出の合流を組み立てる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：指定した先行行の選択語と終端の除外状態の証跡（BF §1.4.4）。
方針：元の再帰と同じ正値性・長さ条件を一行ずつ記録する。
規約：空の先行部分は除外状態を変えない。
使われ方：任意の位置で元の抽出を前後に分けて再構成する。 -/
inductive ExtractionPrefix : List (List α × ℕ) → List α → List (List α) → List α → Prop
  | nil (removed : List α) : ExtractionPrefix [] removed [] removed
  | cons {row : List α} {r : ℕ} {rest : List (List α × ℕ)}
      {removed : List α} {picked : List (List α)} {finish : List α}
      (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
      (tail : ExtractionPrefix rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1))
        picked finish) :
      ExtractionPrefix ((row, r) :: rest) removed ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r :: picked)
        finish

/-- 概要：先行部分の証跡と終端からの抽出を連結できる（BF §1.4.4）。
方針：証跡の各行の成功を既存 reduceRows に再構成する。
規約：後続の行と出力は任意。
使われ方：変更した中間行の後に削除行以降の抽出をつなぐ。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.append {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish)
    (rest : List (List α × ℕ)) (out : List α) (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest finish = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) removed = some (picked.flatten ++ out) := by
  induction h with
  | nil => simpa only [List.nil_append, List.flatten_nil] using ht
  | cons hr hb htail ih =>
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success _ _ _ _ _ hr hb (ih ht)
    simpa only [List.cons_append, List.flatten_cons, List.append_assoc] using hs

/-- 概要：成功した抽出を任意の行位置で先行部分と後続に分ける（BF §1.4.4）。
方針：先行行で帰納し、元の抽出の一段の成功を保持する。
規約：出力の先行部分は選択行の平坦化。
使われ方：二つの相殺対象の行の間の実際の状態を取り出す。 -/
lemma extractionPrefix_of_reduceRows (before rest : List (List α × ℕ))
    (removed out : List α) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) removed = some out) :
    ∃ picked finish tail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest finish = some tail ∧ out = picked.flatten ++ tail := by
  induction before generalizing removed out with
  | nil => exact ⟨[], removed, out, .nil removed, h, by simp⟩
  | cons p before ih =>
    obtain ⟨hr, hb, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨picked, finish, post, hp, hpost, hout⟩ := ih _ _ ht
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 :: picked, finish, post,
      .cons hr hb hp, hpost, ?_⟩
    rw [he, hout, List.flatten_cons, List.append_assoc]

/-- 概要：先行部分の各選択行の長さは指定された行長（BF §1.4.4）。
方針：take の長さと証跡の帰納法を使う。
規約：選択行と元の行の順序を保つ。
使われ方：削除位置の先行部分の長さを行長から計算する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.lengths {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) :
    picked.map List.length = before.map Prod.snd := by
  induction h with
  | nil => rfl
  | cons hr hb ht ih =>
    simp only [List.map_cons, List.length_take, Nat.min_eq_left hb, ih]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
