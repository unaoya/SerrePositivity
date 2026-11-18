module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DonorStep

/-!
模型。文献の定義との比較は後で
# 受け取り行の延長と削除値の早い除外

概要：Berger–Fresse §1.4.4 の行長を 1 増やす側の抽出を計算する。
方針：後続に残る別の値から利用可能行の余裕を導き、take を一文字延ばす。
規約：増分の arity 上界だけでなく、実際の利用可能行の長さを検証する。
使われ方：長くした受け取り行の後を中間行の輸送へつなぐ。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：後続出力の値は既に除外された状態に属さない（BF §1.4.4）。
方針：抽出証跡の除外値の不出現を実際の出力に移す。
規約：元の行の全射性・重複のなさは不要。
使われ方：後続の別の値から受け取り行の利用可能長の余裕を導く。 -/
lemma not_mem_removed_of_mem_output (rows : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some out) (a : α) (ha : a ∈ out) : a ∉ removed := by
  obtain ⟨picked, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows rows removed out h
  intro hm
  exact hp.removed_not_mem_output a hm (he.symm ▸ ha)

/-- 概要：後続に現在行末と異なる値があれば現在行をさらに一文字取れる（BF §1.4.4）。
方針：その値は今回の除外にも行末にも属さず、利用可能行には残っている。
規約：後続の別の値が現在の元の行に含まれることを要求する。
使われ方：成功 table の受け取り行に実際の一文字の余裕を与える。 -/
lemma receiver_capacity_of_tail (removed row : List α) (r : ℕ) (a c : α)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ++ [a])
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) = some tail)
    (hc : c ∈ tail) (hrow : c ∈ row) (hne : c ≠ a) : r < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
  have hno := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.not_mem_removed_of_mem_output rest _ tail ht c hc
  have hremoved : c ∉ removed := fun hm => hno (List.mem_append_left _ hm)
  have hprefix : c ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) :=
    fun hm => hno (List.mem_append_right _ hm)
  have havail : c ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, decide_eq_true_eq]
    exact ⟨hrow, hremoved⟩
  have hselected : c ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r := by
    rw [he]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hprefix, hne⟩
  by_contra hb
  have heq : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row :=
    List.take_of_length_le (by omega)
  exact hselected (heq.symm ▸ havail)

/-- 概要：正の選択長をさらに一文字延ばすと二つの行末が指定できる（BF §1.4.4）。
方針：take の末尾を評価する公式を二回使う。
規約：利用可能行の長さに厳密な余裕がある。
使われ方：元の行末 a と相殺側で新たに取る行末 b を指定する。 -/
lemma receiver_endpoints (removed row : List α) (r : ℕ) (hr : 0 < r)
    (hb : r < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length) :
    ∃ a b, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ++ [a] ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ [b] := by
  have hi : r - 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row)[r - 1], (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row)[r], ?_, ?_⟩
  · have he := List.take_succ_eq_append_getElem hi
    have heq : r - 1 + 1 = r := by omega
    simpa only [heq] using he
  · exact List.take_succ_eq_append_getElem hb

/-- 概要：長い受け取り行は元の末尾値を早く除外し、新しい行末を一つ加える（BF §1.4.4）。
方針：長い行の除外状態を元の除外状態に末尾値を加えたものと一致させる。
規約：変更後の後続抽出を与えると、元の reduceRows で再構成する。
使われ方：受け取り行を中間行・短い削除行の抽出へ連結する。 -/
lemma reduceRows_receiver_step (removed row : List α) (r : ℕ) (a b : α)
    (hb : r < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
    (ha : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ++ [a])
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ [b])
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      ((removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) ++ [a]) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + 1) :: rest) removed =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ [b]) ++ tail) := by
  have hs : removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r + 1) - 1) =
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) ++ [a] := by
    rw [Nat.add_sub_cancel, ha, List.append_assoc]
  have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r + 1) - 1)) = some tail := by
    rw [hs]
    exact ht
  have hsuccess := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (r + 1) rest removed tail
    (by omega) (by omega) htail
  rw [he] at hsuccess
  exact hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
