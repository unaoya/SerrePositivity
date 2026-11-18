module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionLabels

/-!
模型。文献の定義との比較は後で
# 重複のない外側語への部分語代入

概要：Berger–Fresse §2.2.6 の切断の片側への代入は、各挿入部分語が重複を持たなければ非零性を保つ。
方針：外側語で帰納し、残りラベルの所属と挿入ラベルとの非交差を使う。
規約：内側 arity 零・空部分語も含み、未消費部分語を許す。
使われ方：非切断点色への一部分割・二部分割の合成切断の左右 Nodup 条件。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定色のない語への代入は残り文字の単射なラベル像（BF §2.2.6）。
方針：指定色を除く部分型へ元の語を持ち上げる。
規約：内側文字の存在を要求せず、arity 零でも成立する。
使われ方：内側ラベルとの非交差を全 arity で示す。 -/
lemma substitute_of_no_slot {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin n))) (hk : k ∉ xs) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k xs hk
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val) parts := by rw [hv]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_word k _ parts

/-- 概要：指定色のない代入像と挿入ラベル像は交わらない（BF §2.2.6）。
方針：両像の所属をそれぞれ残りラベルと挿入ラベルへ戻す。
規約：内側 arity 零を含む。
使われ方：指定色を一度消費した後の語とその挿入部分語を連結する。 -/
lemma substitute_disjoint_inserted_no_slot {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (inner : List (Fin n))
    (hk : k ∉ xs) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).Disjoint (inner.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_of_no_slot k xs parts hk]
  apply List.disjoint_left.mpr
  intro a ha hai
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, _, he⟩ := List.mem_map.mp hai
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k x y he.symm

/-- 概要：代入語の残りラベルの所属は元の外側文字の所属と同値（BF §2.2.6）。
方針：外側語で帰納し、指定色では挿入ラベルとの非交差、他の色では残りラベルの単射性を使う。
規約：部分語数・語長への仮定なし。
使われ方：重複のない外側文字が代入後にも一回しか現れないこと。 -/
lemma remaining_mem_substitute_iff {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin n))) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts ↔ a.val ∈ xs := by
  induction xs generalizing parts with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.not_mem_nil]
  | cons x xs ih =>
    by_cases hx : x = k
    · subst x
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.mem_append]
      have hn : _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a ∉
          (parts.headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) := by
        intro hm
        obtain ⟨b, _, he⟩ := List.mem_map.mp hm
        exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k a b he.symm
      simp only [hn, false_or, ih, List.mem_cons, a.property, false_or]
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hx, List.mem_cons, ih, List.mem_cons]
      have he : _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a =
          _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨x, hx⟩ ↔ a.val = x := by
        constructor
        · intro h
          exact congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k h)
        · intro h
          exact congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) (Subtype.ext h)
      rw [he]

/-- 概要：重複のない外側語へ重複のない部分語を代入しても重複は生じない（BF §2.2.6）。
方針：指定色は高々一回であり、残りラベルと挿入ラベルの非交差を帰納的に使う。
規約：各部分語の Nodup だけを要求し、部分語同士の非交差は要求しない。
使われ方：外側切断の左右に内側切断の二つの非零部分語を代入する。 -/
lemma substitute_nodup_of_parts {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin n))) (hx : xs.Nodup) (hp : ∀ part ∈ parts, part.Nodup) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).Nodup := by
  induction xs generalizing parts with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.nodup_nil]
  | cons x xs ih =>
    have hnot := (List.nodup_cons.mp hx).1
    have hxs := (List.nodup_cons.mp hx).2
    by_cases hxk : x = k
    · subst x
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl]
      have hhead : (parts.headD []).Nodup := by
        cases parts with
        | nil => exact List.nodup_nil
        | cons part parts => exact hp part (List.mem_cons_self ..)
      have htail : ∀ part ∈ parts.tail, part.Nodup := by
        intro part hpart
        exact hp part (List.mem_of_mem_tail hpart)
      exact (hhead.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k)).append
        (ih parts.tail hxs htail) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_disjoint_inserted_no_slot k xs parts.tail
          (parts.headD []) hnot).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hxk, List.nodup_cons]
      refine ⟨?_, ih parts hxs hp⟩
      intro hm
      exact hnot ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_mem_substitute_iff k ⟨x, hxk⟩ xs parts).mp hm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
