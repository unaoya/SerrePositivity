module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReceiverStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixExclusions

/-!
模型。文献の定義との比較は後で
# 行末側で一行を短くして直前値の除外を解く

概要：Berger–Fresse §1.4.4 の行末削除の逆構成の最初の状態を作る。
方針：二つの末尾値を取り、選択長を一つ減らすと直前値が次の除外から外れることを計算する。
規約：元の選択長は 2 以上、行と除外状態は重複を持たない。
使われ方：実際の逆探索へ初期の重複のなさ・解放値の不所属・二状態の関係を渡す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：長い行の最後の二値を分け、短縮後は前の値の除外が解かれる（BF §1.4.4）。
方針：二つの take の末尾公式と重複のなさ、一行の先行抽出を使う。
規約：変更後の短い行長は r−1 で正。
使われ方：残余の区切り行末を短くして後続行の逆探索を開始する。 -/
lemma receiver_release (removed row : List α) (r : ℕ) (hn : removed.Nodup)
    (hrow : row.Nodup) (hr : 1 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length) :
    ∃ pre a b free,
      pre.length + 2 = r ∧ a ≠ b ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r = pre ++ [a, b] ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) = pre ++ [a] ∧
      free = removed ++ pre ∧ free.Nodup ∧ a ∉ free ∧
      removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) = free ++ [a] ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(row, r - 1)] removed = some (pre ++ [a]) := by
  have hshort : 0 < r - 1 := by omega
  have hcapacity : r - 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
  obtain ⟨a, b, ha, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.receiver_endpoints removed row (r - 1) hshort hcapacity
  let pre := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r - 1) - 1)
  let free := removed ++ pre
  have hlength : pre.length + 2 = r := by
    have hle : (r - 1) - 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
    simp only [pre, List.length_take, Nat.min_eq_left hle]
    omega
  have hfull : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r = pre ++ [a, b] := by
    have hlen : (r - 1) + 1 = r := by omega
    rw [hlen, ha] at he
    simpa only [pre, List.append_assoc, List.singleton_append] using he
  have hselected : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) = pre ++ [a] := ha
  have hprefix : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, r - 1)] removed
      [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)] free := .cons hshort (by omega) (.nil free)
  have hfree : free.Nodup := hprefix.finish_nodup hn (by
    intro p hp
    have hp' : p = (row, r - 1) := List.mem_singleton.mp hp
    simpa only [hp'] using hrow)
  have hraw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).Nodup := hrow.filter _
  have htwo : (pre ++ [a, b]).Nodup := (congrArg List.Nodup hfull).mp hraw.take
  have hab : a ≠ b := by
    simpa only [List.mem_singleton] using (List.nodup_cons.mp (List.nodup_append.mp htwo).2.1).1
  have hshortNodup : (pre ++ [a]).Nodup :=
    (congrArg List.Nodup hselected).mp hraw.take
  have haPre : a ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hshortNodup).2.2 a hm a (by simp) rfl
  have haRemoved : a ∉ removed := by
    have hm : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by rw [hselected]; simp
    have hall := List.mem_of_mem_take hm
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, decide_eq_true_eq] at hall
    exact hall.2
  have hstate : removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) = free ++ [a] := by
    rw [hselected, List.append_assoc]
  have htake := hprefix.append [] [] (by rfl)
  refine ⟨pre, a, b, free, hlength, hab, hfull, hselected, rfl, hfree, ?_, hstate, ?_⟩
  · simp only [free, List.mem_append, not_or]
    exact ⟨haRemoved, haPre⟩
  · simpa only [List.append_nil, List.flatten_cons, List.flatten_nil,
      hselected] using htake

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
