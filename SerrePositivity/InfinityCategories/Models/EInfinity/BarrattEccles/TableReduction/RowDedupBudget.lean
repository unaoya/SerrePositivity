module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows
public import Mathlib.Data.List.Dedup

/-!
模型。文献の定義との比較は後で
# 各行末だけが失われ得るという重複除去の計数

概要：Berger–Fresse §1.4.4 の行末の再出現を語の長さから強制する。
方針：行の内部の値は全て最終出現なので、重複除去が失うのは各非最終行末の高々一文字。
規約：各行は非空で行の分離条件を満たす。
使われ方：長さ n+d と値集合の濃度 n から全ての非最終行末の再出現を導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：一行を前に足した重複除去の長さ（BF §1.4.4）。
方針：末尾以外は後続と互いに素で、末尾だけは後続への所属によって分岐する。
規約：元の行は重複せず、非空。
使われ方：一行が失う文字の個数を 0 または 1 として数える。 -/
lemma dedup_length_prepend_row (row tail : List α) (hr : row ≠ []) (hn : row.Nodup)
    (hf : ∀ a ∈ row.dropLast, a ∉ tail) :
    (row ++ tail).dedup.length = row.length - 1 + tail.dedup.length +
      if row.getLast hr ∈ tail then 0 else 1 := by
  let a := row.getLast hr
  have hsplit : row.dropLast ++ [a] = row := List.dropLast_append_getLast hr
  have hnp : (row.dropLast ++ [a]).Nodup := by rw [hsplit]; exact hn
  have hna : a ∉ row.dropLast := by
    intro ha
    exact (List.nodup_append.mp hnp).2.2 a ha a (by simp) rfl
  have hd : List.Disjoint row.dropLast (a :: tail) := by
    intro x hx hy
    rcases List.mem_cons.mp hy with he | ht
    · subst x
      exact hna hx
    · exact hf x hx ht
  have he : row ++ tail = row.dropLast ++ a :: tail := by
    rw [← List.singleton_append, ← List.append_assoc, hsplit]
  rw [he, hd.dedup_append, (List.nodup_append.mp hnp).1.dedup, List.dedup_cons]
  dsimp only [a]
  by_cases ha : row.getLast hr ∈ tail <;>
    simp only [ha, ↓reduceIte, List.length_append, List.length_cons, List.length_dropLast] <;>
    omega

/-- 概要：分離した非空の行の連結では重複除去の損失は行数−1 以下（BF §1.4.4）。
方針：一行ごとの損失の上界を帰納的に足す。
規約：最後の行は重複せず、損失を生じない。
使われ方：table の全行末が再出現することを計数で強制する。 -/
lemma separatedRows_length_le (picked : List (List α)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked →
    (∀ row ∈ picked, row ≠ []) →
    picked.flatten.length ≤ picked.flatten.dedup.length + (picked.length - 1) := by
  induction picked with
  | nil => intro _ _; simp
  | cons row rest ih =>
    intro hs hne
    have hr := hne row (List.mem_cons_self ..)
    have hpos : 0 < row.length := List.length_pos_iff.mpr hr
    have hnrest : ∀ r ∈ rest, r ≠ [] := fun r hm => hne r (List.mem_cons_of_mem _ hm)
    have hb := ih hs.2.2 hnrest
    cases rest with
    | nil =>
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_nil, Nat.add_sub_cancel, Nat.add_zero] using le_of_eq (hs.1.dedup.symm ▸ rfl)
    | cons next rest =>
      have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_prepend_row row ((next :: rest).flatten) hr hs.1 hs.2.1
      simp only [List.flatten_cons, List.length_append, List.length_cons] at hb hd ⊢
      by_cases ha : row.getLast hr ∈ (next :: rest).flatten <;>
        simp only [List.flatten_cons] at ha <;>
        simp only [ha, ↓reduceIte] at hd <;> omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
