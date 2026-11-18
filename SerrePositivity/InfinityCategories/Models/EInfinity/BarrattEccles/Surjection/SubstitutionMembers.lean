module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution

/-!
模型。文献の定義との比較は後で
# リスト代入で保持される内外の値

概要：Berger–Fresse §1.2.4 の合成語に内側・残りの外側の値が現れることを示す。
方針：外側語で帰納し、指定値で部分語を消費する場合だけ内側の所属を分ける。
規約：部分語数は内側の主張でだけ出現回数に合わせる。
使われ方：全射語の合成の全射性を元の二つの全射性へ帰着する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値以外の外側の値は代入後にも現れる（BF §1.2.4）。
方針：外側語の該当位置を帰納法で追跡する。
規約：部分語の個数・長さ・値には制約しない。
使われ方：合成語に残りの外側入力が全て現れることを示す。 -/
lemma remaining_mem_substitute {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (a : Fin (m + 1)) (ha : a ≠ k) (hm : a ∈ xs) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨a, ha⟩ ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts := by
  induction xs generalizing parts with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases hx : x = k
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left hx]
      apply List.mem_append_right
      apply ih parts.tail
      rcases List.mem_cons.mp hm with he | hm
      · exact False.elim (ha (he.trans hx))
      · exact hm
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hx]
      rcases List.mem_cons.mp hm with he | hm
      · subst x
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih parts hm)

/-- 概要：全ての挿入部分語の値は代入後にも現れる（BF §1.2.4）。
方針：指定値の行では先頭部分語と後続部分語の所属に分ける。
規約：部分語数は指定値の出現回数と一致する。
使われ方：内側語を覆う分割から合成語の内側入力の全射性を得る。 -/
lemma inserted_mem_substitute {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hc : parts.length = xs.count k) (a : Fin n) (ha : a ∈ parts.flatten) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts := by
  induction xs generalizing parts with
  | nil =>
    have hp : parts = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    simp only [hp, List.flatten_nil, List.not_mem_nil] at ha
  | cons x xs ih =>
    by_cases hx : x = k
    · subst x
      cases parts with
      | nil => simp at hc
      | cons part parts =>
        have ht : parts.length = xs.count k := by simpa using hc
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons]
        rcases List.mem_append.mp ha with hm | hm
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨a, hm, rfl⟩)
        · exact List.mem_append_right _ (ih parts ht hm)
    · have ht : parts.length = xs.count k := by simpa [hx] using hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hx]
      exact List.mem_cons_of_mem _ (ih parts ht ha)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
