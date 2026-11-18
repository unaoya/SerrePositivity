module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionOneSlot
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RemainingLettersValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalLabelImages

/-!
模型。文献の定義との比較は後で
# 一出現の前後の非交差ラベル

概要：Berger–Fresse §2.2.6 の一出現挿入の前後には指定色がなく、内側ラベルと交わらない。
方針：出現の一意性と残り文字の復元を使い、代入を単射な水平ラベル写像へ直す。
規約：内側文字 b は存在する辺切断から得る。
使われ方：一出現の合成切断の左右リストの重複消滅。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現色の任意の位置は唯一位置に一致（BF §1.2.4）。
方針：全出現の列挙に戻して一元添字の一意性を使う。
規約：語の全射性・非退化性を要求しない。
使われ方：唯一位置の前後の指定色の不出現。 -/
lemma position_eq_of_count_one {n l : ℕ} (u : Fin l → Fin n) (k : Fin n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k = 1) (p : Fin l) (hp : u p = k) (i : Fin l) (hi : u i = k) :
    i = p := by
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete u k i hi
  exact hj.symm.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceAt_of_count_one u k hc p hp j)

/-- 概要：唯一の指定色の位置より前の語にはその色はない（BF §2.2.6）。
方針：部分リストの所属を元位置へ戻し、出現一意性で排除する。
規約：唯一位置そのものを接頭語に含めない。
使われ方：前半の代入を単なるラベル写像へ直す。 -/
lemma single_slot_not_mem_prefix {n l : ℕ} (u : Fin l → Fin n) (k : Fin n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k = 1) (p : Fin l) (hp : u p = k) :
    k ∉ (List.ofFn u).take p.val := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice u k 0 p.val (by
    intro i _ hi he
    have hv := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.position_eq_of_count_one u k hc p hp i he)
    omega)
  simpa only [List.drop_zero, Nat.sub_zero] using H

/-- 概要：唯一の指定色の位置より後の語にはその色はない（BF §2.2.6）。
方針：指定位置の直後から語末までの部分リストで出現一意性を使う。
規約：唯一位置の次から接尾語を取る。
使われ方：後半の代入を単なるラベル写像へ直す。 -/
lemma single_slot_not_mem_suffix {n l : ℕ} (u : Fin l → Fin n) (k : Fin n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k = 1) (p : Fin l) (hp : u p = k) :
    k ∉ (List.ofFn u).drop (p.val + 1) := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice u k (p.val + 1) l (by
    intro i hi _ he
    have hv := congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.position_eq_of_count_one u k hc p hp i he)
    omega)
  have hl : ((List.ofFn u).drop (p.val + 1)).length = l - (p.val + 1) := by
    simp only [List.length_drop, List.length_ofFn]
  rw [← hl, List.take_length] at H
  exact H

/-- 概要：指定色のない語への任意部分語列の代入は水平ラベル像（BF §2.2.6）。
方針：残り文字の部分型へ持ち上げ、指定色のない語の代入公式を使う。
規約：残った内側部分語列に依存しない。
使われ方：一出現挿入の前半と後半の Nodup 条件。 -/
lemma substitute_no_slot_horizontalLabel_parts {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (hk : k ∉ xs) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts = xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k xs hk
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val) parts := by rw [hv]
    _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_word k _ parts
    _ = _ := by
      conv_rhs => rw [← hv]
      simp only [List.map_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_remaining, Function.comp_def]

/-- 概要：指定色のない重複のない語への代入は重複を作らない（BF §2.2.6）。
方針：単射な水平ラベル写像による像へ直す。
規約：内側部分語列は任意。
使われ方：合成切断の左右に置く外側リストの Nodup 条件。 -/
lemma substitute_nodup_of_no_slot {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (hk : k ∉ xs) (hx : xs.Nodup) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).Nodup := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_no_slot_horizontalLabel_parts k b xs parts hk]
  exact hx.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_injective k b)

/-- 概要：指定色のない外側の代入像は内側ラベル像と交わらない（BF §2.2.6）。
方針：外側像を残りラベルへ戻して挿入ラベルとの非一致を使う。
規約：二つの元のリストの文字や長さは任意。
使われ方：左右の切断リストを内側の切断リストと連結する。 -/
lemma substitute_disjoint_inserted {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (inner : List (Fin n))
    (hk : k ∉ xs) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).Disjoint (inner.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_no_slot_horizontalLabel_parts k b xs parts hk]
  apply List.disjoint_left.mpr
  intro a ha hai
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, _, he⟩ := List.mem_map.mp hai
  have hxk : x ≠ k := fun h => hk (h ▸ hx)
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_remaining k b ⟨x, hxk⟩
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k ⟨x, hxk⟩ y (hr.symm.trans he.symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
