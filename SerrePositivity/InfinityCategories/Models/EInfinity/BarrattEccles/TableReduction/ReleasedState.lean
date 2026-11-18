module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixExclusions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntermediateStep

/-!
模型。文献の定義との比較は後で
# 解放値をまだ選ばない一行の状態遷移

概要：Berger–Fresse §1.4.4 の逆探索で、影響を受けない行を通過する。
方針：選択部分の不変性と一行の先行抽出の除外計数を使う。
規約：解放値は選択先頭 r 文字にも除外状態にも属さない。
使われ方：探索の帰納法で重複のなさ・解放値の不所属・予算を保つ。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：解放値を選ばない一行の後で状態の計数と一文字の差を保つ（BF §1.4.4）。
方針：先行抽出証跡から重複のなさと長さを得て、二つの除外の所属を比較する。
規約：元の行と除外状態は重複を持たない。
使われ方：逆探索を次の行へ進める実際の状態を供給する。 -/
lemma released_state_step (removed row : List α) (a : α) (r : ℕ)
    (hn : removed.Nodup) (hrow : row.Nodup) (ha : a ∉ removed)
    (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
    (hx : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r) :
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)).Nodup ∧
      a ∉ removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ∧
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)).length = removed.length + (r - 1) ∧
      ∀ x, x ∈ (removed ++ [a]) ++
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (r - 1) ↔
        x ∈ (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) ++ [a] := by
  let finish := removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, r)] removed [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r] finish :=
    .cons hr hb (.nil finish)
  have hfinish : finish.Nodup := ht.finish_nodup hn (by
    intro p hp
    have he : p = (row, r) := List.mem_singleton.mp hp
    simpa only [he] using hrow)
  have hl := ht.finish_length
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hl
  have hno : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by
    intro hm
    have he : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).take (r - 1) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by
      rw [List.take_take, Nat.min_eq_left (Nat.sub_le r 1)]
    rw [← he] at hm
    exact hx (List.mem_of_mem_take hm)
  refine ⟨hfinish, ?_, hl, ?_⟩
  · simp only [List.mem_append, not_or]
    exact ⟨ha, hno⟩
  · intro x
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.intermediate_excluded_eq removed row a r hx]
    simp only [List.mem_append, List.mem_singleton]
    tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
