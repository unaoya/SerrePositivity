module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotOutputLists

/-!
模型。文献の定義との比較は後で
# 代入語での挿入ラベルの所属

概要：Berger–Fresse §2.2.6 の代入語に現れる挿入色を消費済み部分語で特徴付ける。
方針：外側語の帰納で指定色だけが次の部分語を消費することを使う。
規約：空部分語・部分語不足・内側 arity 零も同じ式で扱う。
使われ方：合成切断の左右の挿入出力頂点を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定色のない代入語には挿入ラベルが現れない（BF §2.2.6）。
方針：代入を残りラベルの map へ戻し、両ラベルの非交差を使う。
規約：未消費の部分語列は任意。
使われ方：一出現挿入の前後のブロックを挿入色の出力から除く。 -/
lemma inserted_not_mem_substitute_of_no_slot {m n : ℕ} (k : Fin (m + 1))
    (b : Fin n) (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (hk : k ∉ xs) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_of_no_slot k xs parts hk]
  intro hm
  obtain ⟨a, _, he⟩ := List.mem_map.mp hm
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k a b he

/-- 概要：代入語の挿入色の所属は消費済み部分語の平坦化への所属（BF §2.2.6）。
方針：外側語で帰納し、指定色で部分語の先頭を連結し、他の色では所属を保つ。
規約：必要な部分語数や正長性を仮定しない。
使われ方：二部分割の前半と後半の内側出力への一致。 -/
lemma inserted_mem_substitute_iff {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts ↔
      b ∈ (parts.take (xs.count k)).flatten := by
  induction xs generalizing parts with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.count_nil, List.take_zero, List.flatten_nil,
      List.not_mem_nil]
  | cons x xs ih =>
    by_cases hx : x = k
    · subst x
      cases parts with
      | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_nil, List.map_nil,
          List.nil_append, List.tail_nil, ih, List.count_cons_self, List.take_nil,
          List.flatten_nil]
      | cons part parts =>
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
          List.mem_append, List.mem_map_of_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k), ih,
          List.count_cons_self, List.take_succ_cons, List.flatten_cons, List.mem_append]
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hx, List.mem_cons]
      have he : _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b ≠
          _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨x, hx⟩ :=
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k ⟨x, hx⟩ b).symm
      simp only [he, false_or, ih, List.count_cons_of_ne hx]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
