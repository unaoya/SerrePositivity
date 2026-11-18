module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows

/-!
模型。文献の定義との比較は後で
# 末尾を保持する抽出先頭部分の射影

概要：Berger–Fresse §1.5.8 の内側射影で選択語と末尾以外の除外を計算する。
方針：射影した先頭部分も先頭部分であり、残す末尾があれば行長は正になる。
規約：行から選ぶ長さ r は正で可用行長以下。射影が末尾を捨てないことを要求する。
使われ方：垂直成分の非最終行を元の内側表の一行の成功へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：先頭部分の filterMap は射影後の同じ長さの先頭部分（BF §1.5.8）。
方針：元の列を take と drop の連結へ分け、射影後も同じ連結を得る。
規約：r に上限や正値性を要求しない。
使われ方：射影した選択語の長さを元の内側行の行長として使う。 -/
lemma filterMap_take_prefix (f : α → Option β) (xs : List α) (r : ℕ) :
    (xs.filterMap f).take ((xs.take r).filterMap f).length = (xs.take r).filterMap f := by
  have he : xs.filterMap f = (xs.take r).filterMap f ++ (xs.drop r).filterMap f := by
    rw [← List.filterMap_append, List.take_append_drop]
  rw [he, List.take_left]

/-- 概要：射影に残る選択末尾は射影行長を正にし、除外更新も保つ（BF §1.5.8）。
方針：選択語を先行部分と末尾一文字へ分け、射影後の長さを一増分として計算する。
規約：末尾の射影値は some。前半の文字は捨ててもよい。
使われ方：元の一行の成功から射影した正の一行の成功を構成する。 -/
lemma filterMap_selection_retained_last (f : α → Option β) (xs : List α) (r : ℕ)
    (hr : 0 < r) (hb : r ≤ xs.length)
    (he : ∃ a b, (xs.take r).getLast? = some a ∧ f a = some b) :
    0 < ((xs.take r).filterMap f).length ∧
      ((xs.take r).filterMap f).length ≤ (xs.filterMap f).length ∧
      (xs.take (r - 1)).filterMap f =
        (xs.filterMap f).take (((xs.take r).filterMap f).length - 1) := by
  have hi : r - 1 < xs.length := by omega
  have hs : xs.take r = xs.take (r - 1) ++ [xs[r - 1]] := by
    have h := List.take_append_getElem hi
    have hi' : r - 1 + 1 = r := by omega
    simpa only [hi'] using h.symm
  obtain ⟨a, b, ha, hf⟩ := he
  have hlast : xs[r - 1] = a := by
    rw [hs, List.getLast?_append] at ha
    simpa only [List.getLast?_singleton, Option.some_or, Option.some.injEq] using ha
  have hproj : (xs.take r).filterMap f =
      (xs.take (r - 1)).filterMap f ++ [b] := by
    rw [hs, List.filterMap_append]
    simp only [List.filterMap_cons, hlast, hf, List.filterMap_nil]
  have hl : ((xs.take r).filterMap f).length =
      ((xs.take (r - 1)).filterMap f).length + 1 := by
    rw [hproj, List.length_append, List.length_singleton]
  refine ⟨by omega, ?_, ?_⟩
  · have h := congrArg List.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix f xs r)
    simp only [List.length_take] at h
    omega
  · rw [hl, Nat.add_sub_cancel, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
