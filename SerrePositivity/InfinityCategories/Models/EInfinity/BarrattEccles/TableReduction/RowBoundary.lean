module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows
public import Mathlib.Data.List.Nodup

/-!
模型。文献の定義との比較は後で
# 同じ置換の隣接行の境界

概要：Berger–Fresse §1.4.1 の退化列の証明に必要な行の除外を計算する。
方針：重複のない行から既に選んだ先頭部分を除くと残りの末尾になることを示す。
規約：前行の最後の文字は除外せず、次行の先頭として残る。
使われ方：等しい隣接頂点を持つ table の出力に隣接重複を見つける。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：先頭部分の値を全て除くと残りの語になる（BF §1.4.1）。
方針：行長とリストで帰納し、重複がないため先頭の値は尾部から除かれない。
規約：元のリストは重複しない。
使われ方：同じ置換の次行の先頭を特定する。 -/
lemma filter_not_mem_take (xs : List α) (hxs : xs.Nodup) (k : ℕ) :
    xs.filter (fun x => x ∉ xs.take k) = xs.drop k := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rcases List.nodup_cons.mp hxs with ⟨ha, ht⟩
      simp only [List.take_succ_cons, List.drop_succ_cons, List.filter_cons,
        List.mem_cons, not_or, not_true_eq_false, false_and, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      have he : xs.filter (fun x => x ≠ a ∧ x ∉ xs.take k) =
          xs.filter (fun x => x ∉ xs.take k) := by
        apply List.filter_congr
        intro x hx
        have hxa : x ≠ a := fun h => ha (h ▸ hx)
        simp [hxa]
      rw [he, ih xs ht]

/-- 概要：先行の除外と今回の除外は filter の反復（BF §1.4.1）。
方針：所属判定と filter の合成を比較する。
規約：除外リストに重複があってもよい。
使われ方：残っている文字列に対して今回の先頭部分だけを除く。 -/
lemma available_append (removed more row : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ more) row = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available more (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases h₁ : x ∈ removed <;> by_cases h₂ : x ∈ more <;> simp [h₁, h₂]

/-- 概要：同じ行を再利用すると前行の最後の文字から続く（BF §1.4.1）。
方針：二段の filter を先頭部分の削除へ簡約する。
規約：k は前行の長さから 1 を引いたものとして使う。
使われ方：退化列の table の境界重複の核心となる。 -/
lemma available_after_take (removed row : List α) (hrow : row.Nodup) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take k) row =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).drop k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_append]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_not_mem_take _ (hrow.filter _) k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
