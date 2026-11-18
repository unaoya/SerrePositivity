module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 成功した抽出の全ての行長の上下界

概要：Berger–Fresse §1.3.1 の抽出成功から全行長の正性と元の行長以下の上界を取り出す。
方針：各実際の成功分岐の正性・利用可能長上界を元の行へ戻す。
規約：先行除外と出力語は任意。
使われ方：全共有行融合表から実際の有限 Schedule を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：抽出に成功した全ての行長は正で元の行長以下（BF §1.3.1）。
方針：先頭成功の長さ条件と後続成功で行数に関して帰納する。
規約：全行が置換であることは要求しない。
使われ方：各選択長さを Schedule の有限型へ包む。 -/
lemma reduceRows_row_bounds {α : Type*} [DecidableEq α]
    (rs : List (List α × ℕ)) (initial out : List α) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs initial = some out) :
    ∀ p ∈ rs, 0 < p.2 ∧ p.2 ≤ p.1.length := by
  induction rs generalizing initial out with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons a rs ih =>
    obtain ⟨row, r⟩ := a
    obtain ⟨hr, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success row r rs initial out h
    intro p hp
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      exact ⟨hr, hb.trans (List.length_filter_le ..)⟩
    · exact ih _ _ ht p hp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
