module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionLabels

/-!
模型。文献の定義との比較は後で
# 非空部分語の代入は隣接非一致を保つ

概要：Berger–Fresse §1.2.4 の正の内側語の合成に隣接重複がないことを示す。
方針：指定値の直後は別の外側ラベルであり、内外ラベルは非交差であることを使う。
規約：部分語数は出現回数に一致し、各部分語は非空で隣接非一致とする。
使われ方：実際の分割部分語へ適用して全合成語の非退化性を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非退化な外側語への非空な非退化部分語の代入は非退化（BF §1.2.4）。
方針：外側語で帰納し、内側部分語の内部・内外の境界・外側の隣接の三つを検査する。
規約：空語挿入の分岐はこの補題を使わず正規化で扱う。
使われ方：正の内側 arity の合成語がそのまま基底語を表すことを示す。 -/
lemma substitute_isChain {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hx : xs.IsChain (· ≠ ·)) (hc : parts.length = xs.count k)
    (hp : ∀ part ∈ parts, part ≠ [] ∧ part.IsChain (· ≠ ·)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).IsChain (· ≠ ·) := by
  induction xs generalizing parts with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.IsChain.nil]
  | cons a xs ih =>
    have htail := hx.tail
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp at hc
      | cons part parts =>
        have hpart := hp part (by simp)
        have hparts : ∀ q ∈ parts, q ≠ [] ∧ q.IsChain (· ≠ ·) := by
          intro q hq
          exact hp q (List.mem_cons_of_mem _ hq)
        have hcount : parts.length = xs.count k := by simpa using hc
        have hrest := ih parts htail hcount hparts
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons]
        apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_map_inserted k part hpart.2).append hrest
        intro x hxlast y hy
        cases xs with
        | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute] at hy
        | cons b xs =>
          have hbk : b ≠ k := (List.isChain_cons_cons.mp hx).1.symm
          have hy' : _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨b, hbk⟩ = y := by
            simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hbk, List.head?_cons, Option.mem_def,
              Option.some.injEq] using hy
          subst y
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_getLast? hxlast)
          exact (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k ⟨b, hbk⟩ c).symm
    · have hcount : parts.length = xs.count k := by simpa [ha] using hc
      have hrest := ih parts htail hcount hp
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha]
      apply List.isChain_cons.mpr
      refine ⟨?_, hrest⟩
      intro y hy
      cases xs with
      | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute] at hy
      | cons b xs =>
        by_cases hb : b = k
        · subst b
          cases parts with
          | nil => simp at hcount
          | cons part parts =>
            have hne := (hp part (by simp)).1
            cases part with
            | nil => exact False.elim (hne rfl)
            | cons c cs =>
              have hy' : _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k c = y := by
                simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
                  List.map_cons, List.cons_append, List.head?_cons, Option.mem_def,
                  Option.some.injEq] using hy
              subst y
              exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k ⟨a, ha⟩ c
        · have hy' : _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨b, hb⟩ = y := by
            simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hb, List.head?_cons, Option.mem_def,
              Option.some.injEq] using hy
          subst y
          intro he
          have hab := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k he
          exact (List.isChain_cons_cons.mp hx).1 (congrArg Subtype.val hab)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
