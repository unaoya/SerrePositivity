module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SegmentPositions

/-!
模型。文献の定義との比較は後で
# 代入後の残り位置と残り色の順序

概要：Berger–Fresse §2.2.6 の代入は指定色以外の位置と色の厳密順序を保つ。
方針：元位置の直後の接頭語長が一増えることと、残り色の番号公式を使う。
規約：内側の空語と任意の重なる分割も含む。
使われ方：外側活動位置の合成後の逆転数の比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定色以外の一文字を越えると代入後の接頭語長は一増える（BF §2.2.6）。
方針：接頭語の末尾一文字を分け、非指定色の代入規則を評価する。
規約：部分語の長さや非退化性を仮定しない。
使われ方：残り位置の厳密単調性。 -/
lemma substitute_prefix_length_at_non_slot {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n))) (p : Fin xs.length)
    (hp : xs[p.val] ≠ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (xs.take (p.val + 1)) parts).length =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (xs.take p.val) parts).length + 1 := by
  rw [List.take_succ_eq_append_getElem p.isLt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute,
    dite_eq_right hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute]
  simp only [List.length_append, List.length_cons, List.length_nil]

/-- 概要：指定色以外の二位置の厳密順序は代入後も保持（BF §2.2.6）。
方針：先の位置を一文字越えた接頭語の長さを後の位置の接頭語長で抑える。
規約：内側 arity 零も含む。
使われ方：合成後の活動位置間の順序を外側へ戻す。 -/
lemma compositeOuterPosition_lt {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (p q : Fin (m + 1 + d)) (hp : u.val p ≠ k) (hq : u.val q ≠ k) (hpq : p < q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r q hq := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (r.segments v.val)
    (show p.val + 1 ≤ q.val from hpq)
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_non_slot k (List.ofFn u.val) (r.segments v.val)
    ⟨p.val, by simpa only [List.length_ofFn] using p.isLt⟩ (by
      simpa only [List.getElem_ofFn] using hp)
  rw [hs] at H
  exact H

/-- 概要：残り位置の厳密順序は代入前後で同値（BF §2.2.6）。
方針：逆向きの順序か等号なら保存済みの厳密順序に矛盾する。
規約：指定色以外の二位置だけに条件を課す。
使われ方：逆転対の位置不等式を元の語へ移す。 -/
lemma compositeOuterPosition_lt_iff {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (p q : Fin (m + 1 + d)) (hp : u.val p ≠ k) (hq : u.val q ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r q hq ↔ p < q := by
  constructor
  · intro H
    rcases lt_trichotomy p q with h | rfl | h
    · exact h
    · exact False.elim (lt_irrefl _ H)
    · exact False.elim (lt_asymm H (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt u v k r q p hq hp h))
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt u v k r p q hp hq

/-- 概要：残り色の番号変更は厳密順序を保ち反映する（BF §2.2.6）。
方針：指定色より前後での番号公式を比較する。
規約：内側 arity 零で指定色を除く場合も含む。
使われ方：合成後の活動色の不等式を外側色へ戻す。 -/
lemma remainingPosition_lt_iff {m n : ℕ} (k : Fin (m + 1))
    (a b : {j : Fin (m + 1) // j ≠ k}) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a < _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b ↔
      a.val < b.val := by
  simp only [Fin.lt_def, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_val, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingValue]
  have ha := a.property
  have hb := b.property
  have hka : a.val.val ≠ k.val := fun h => ha (Fin.ext h)
  have hkb : b.val.val ≠ k.val := fun h => hb (Fin.ext h)
  split_ifs <;> omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
