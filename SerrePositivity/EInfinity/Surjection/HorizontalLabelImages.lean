module

public import SerrePositivity.EInfinity.Surjection.HorizontalLabels

/-!
# 水平ラベル写像の単射性と像の所属

概要：Berger–Fresse §1.5.7 の最終水平成分で任意の追加除外を水平ラベルへ移す。
方針：指定値と他の外側文字の像を内外ラベルの直和分解で区別する。
規約：固定した内側の一文字へ指定値を送る。
使われ方：指定値自身を最終除外する更新も合成状態へ移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles

/-- 概要：固定した内側文字を使う水平ラベル写像は単射（BF §1.5.7）。
方針：内外ラベルの非交差と残りラベル写像の単射性を使う。
規約：外側指定値の像は一つの挿入ラベル。
使われ方：水平ラベル像の除外所属を元の外側所属へ戻す。 -/
lemma horizontalLabel_injective {m n : ℕ} (k : Fin (m + 1)) (b : Fin n) :
    Function.Injective (horizontalLabel k b) := by
  intro a c he
  by_cases ha : a = k
  · subst a
    by_cases hc : c = k
    · exact hc.symm
    · have hv := horizontalLabel_remaining k b ⟨c, hc⟩
      rw [horizontalLabel_slot, hv] at he
      exact False.elim (remainingPosition_ne_inserted m n k ⟨c, hc⟩ b he.symm)
  · by_cases hc : c = k
    · subst c
      have hv := horizontalLabel_remaining k b ⟨a, ha⟩
      rw [hv, horizontalLabel_slot] at he
      exact False.elim (remainingPosition_ne_inserted m n k ⟨a, ha⟩ b he)
    · have hv := horizontalLabel_remaining k b ⟨a, ha⟩
      have hw := horizontalLabel_remaining k b ⟨c, hc⟩
      rw [hv, hw] at he
      exact congrArg Subtype.val (remainingPosition_injective m n k he)

/-- 概要：残り外側ラベルの水平像所属は元の所属（BF §1.5.7）。
方針：同じ水平ラベルの値と単射性を使う。
規約：指定値以外の外側文字。
使われ方：最終水平成分の外側除外更新を計算する。 -/
@[simp] lemma remaining_mem_horizontal_map {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (a : {a : Fin (m + 1) // a ≠ k}) :
    remainingPosition m n k a ∈ xs.map (horizontalLabel k b) ↔ a.val ∈ xs := by
  rw [← horizontalLabel_remaining k b a,
    List.mem_map_of_injective (horizontalLabel_injective k b)]

/-- 概要：挿入ラベルの水平像所属は固定文字と指定値の所属で決まる（BF §1.5.7）。
方針：固定文字の像には単射性、他の挿入ラベルには内外の非交差を使う。
規約：水平像に含まれる内側ラベルは固定した一文字だけ。
使われ方：指定値の最終除外で最後の内側文字も除外する。 -/
@[simp] lemma inserted_mem_horizontal_map {m n : ℕ} (k : Fin (m + 1)) (b c : Fin n)
    (xs : List (Fin (m + 1))) :
    insertedPosition m n k c ∈ xs.map (horizontalLabel k b) ↔ c = b ∧ k ∈ xs := by
  by_cases hc : c = b
  · subst c
    rw [← horizontalLabel_slot k b,
      List.mem_map_of_injective (horizontalLabel_injective k b)]
    simp only [true_and]
  · have hn : insertedPosition m n k c ∉ xs.map (horizontalLabel k b) := by
      intro hm
      obtain ⟨a, _, he⟩ := List.mem_map.mp hm
      by_cases ha : a = k
      · subst a
        have hv := (horizontalLabel_slot k b).symm.trans he
        exact hc (insertedPosition_injective m n k hv).symm
      · have hv := (horizontalLabel_remaining k b ⟨a, ha⟩).symm.trans he
        exact remainingPosition_ne_inserted m n k ⟨a, ha⟩ c hv
    simp only [hn, hc, false_and]

end SerrePositivity.EInfinity.Surjection
