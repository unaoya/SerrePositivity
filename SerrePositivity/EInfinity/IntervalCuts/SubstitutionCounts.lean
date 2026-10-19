module

public import SerrePositivity.EInfinity.IntervalCuts.SubstitutionNodup
public import SerrePositivity.EInfinity.IntervalCuts.CompositionCutPositions
public import SerrePositivity.EInfinity.IntervalCuts.CompositionSlotGeometry

/-!
# 合成切断からの残りラベルの復元

概要：Berger–Fresse §2.2.6 の合成語で、挿入されない色の出現数と切断位置を復元する。
方針：代入のリスト帰納で出現数を保存し、非零切断の切断点色の一意性を使う。
規約：出現数の保存は零 arity を含み、実際の合成基底語は正 arity で扱う。
使われ方：二段切断と非零合成切断の有限対応の逆方向。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：代入は残りラベルの出現回数を保存する（BF §2.2.6）。
方針：外側語で帰納し、挿入部分語には残りラベルが現れないことを使う。
規約：部分語数・内側 arity・語長への仮定なし。
使われ方：合成切断の切断点色の一出現を外側語へ戻す。 -/
lemma remaining_count_substitute {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin n))) :
    (substitute k xs parts).count (BarrattEccles.remainingPosition m n k a) =
      xs.count a.val := by
  induction xs generalizing parts with
  | nil => simp only [substitute, List.count_nil]
  | cons x xs ih =>
    by_cases hx : x = k
    · subst x
      rw [substitute, dite_eq_left rfl, List.count_append, ih]
      have hn : BarrattEccles.remainingPosition m n k a ∉
          (parts.headD []).map (BarrattEccles.insertedPosition m n k) := by
        intro hm
        obtain ⟨b, _, he⟩ := List.mem_map.mp hm
        exact BarrattEccles.remainingPosition_ne_inserted m n k a b he.symm
      simp only [List.count_eq_zero.mpr hn, zero_add,
        List.count_cons_of_ne (Ne.symm a.property)]
    · rw [substitute, dite_eq_right hx]
      by_cases ha : a.val = x
      · have he : BarrattEccles.remainingPosition m n k a =
            BarrattEccles.remainingPosition m n k ⟨x, hx⟩ :=
          congrArg (BarrattEccles.remainingPosition m n k) (Subtype.ext ha)
        rw [← he, List.count_cons_self, ih, ← ha, List.count_cons_self]
      · have he : BarrattEccles.remainingPosition m n k ⟨x, hx⟩ ≠
            BarrattEccles.remainingPosition m n k a := by
          intro h
          exact ha (congrArg Subtype.val (remainingPosition_injective m n k h)).symm
        rw [List.count_cons_of_ne he, ih, List.count_cons_of_ne (Ne.symm ha)]

/-- 概要：実際の合成基底語でも残り色の出現回数は外側語と一致（BF §2.2.6）。
方針：合成基底語のリストを代入語へ展開する。
規約：正の内側 arity、任意の重なる分割。
使われ方：非零合成切断から外側の出現数条件を回収する。 -/
lemma composite_remaining_occurrenceCount {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (a : {a : Fin (m + 1) // a ≠ k}) :
    occurrenceCount (compositeBasisWord u v k r hn).val
      (BarrattEccles.remainingPosition m n k a) = occurrenceCount u.val a.val := by
  simp only [occurrenceCount, compositeBasisWord_list, compositeWord,
    remaining_count_substitute]

/-- 概要：非零合成切断の残り色は外側語でも高々二出現（BF §2.2.6）。
方針：合成切断の出現数上限を保存公式で戻す。
規約：切断点色以外も含む全ての残り色。
使われ方：逆方向の外側切断の出現分類。 -/
lemma outer_remaining_occurrenceCount_le_two {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (hq : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (a : {a : Fin (m + 1) // a ≠ k}) : occurrenceCount u.val a.val ≤ 2 := by
  rw [← composite_remaining_occurrenceCount u v k r hn a]
  exact occurrenceCount_le_two_of_cut _ q hq _

/-- 概要：合成切断点が残り色なら、その外側色は一度しか現れない（BF §2.2.6）。
方針：切断点色の一出現と残りラベルの出現数保存を組み合わせる。
規約：切断点のラベルを残り色として明示的に指定する。
使われ方：逆方向に復元する外側位置の一意性。 -/
lemma outer_pivot_occurrenceCount_eq_one {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (hq : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (a : {a : Fin (m + 1) // a ≠ k})
    (ha : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.remainingPosition m n k a) : occurrenceCount u.val a.val = 1 := by
  rw [← composite_remaining_occurrenceCount u v k r hn a, ← ha]
  exact occurrenceCount_pivot_eq_one _ q hq

/-- 概要：残り色の合成切断点は元の外側位置の合成位置に一致（BF §2.2.6）。
方針：外側の同色位置を合成語に送り、合成切断点色の一意性を適用する。
規約：外側切断の非零性を仮定せず位置を復元する。
使われ方：有限全単射の逆方向で外側切断候補を決める。 -/
lemma composite_pivot_eq_outerPosition {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (hq : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (ha : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.remainingPosition m n k ⟨u.val p, hp⟩) :
    q = compositeOuterPosition u v k r p hp := by
  exact (pivot_unique hq _ ((compositeBasisWord_outerPosition u v k r hn p hp).trans
    ha.symm)).symm

/-- 概要：残り色の非零合成切断には一意な外側位置が対応する（BF §2.2.6）。
方針：外側語の全射性で位置を取り、一出現性と合成切断点の一意性で照合する。
規約：外側の非零切断性を結論へ混ぜず、位置と色だけを復元する。
使われ方：逆方向の外側切断候補を選び、その後に左右の非零性を証明する。 -/
lemma exists_unique_outer_pivot {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (hq : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (a : {a : Fin (m + 1) // a ≠ k})
    (ha : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.remainingPosition m n k a) :
    ∃! p : Fin (m + 1 + d), u.val p = a.val ∧
      ∃ hp : u.val p ≠ k, q = compositeOuterPosition u v k r p hp := by
  obtain ⟨p, hp⟩ := u.surjective a.val
  have hpk : u.val p ≠ k := fun h => a.property (hp.symm.trans h)
  have hc := outer_pivot_occurrenceCount_eq_one u v k r hn q hq a ha
  refine ⟨p, ⟨hp, hpk, ?_⟩, ?_⟩
  · apply composite_pivot_eq_outerPosition u v k r hn q hq p hpk
    simpa only [show (⟨u.val p, hpk⟩ : {x : Fin (m + 1) // x ≠ k}) = a from
      Subtype.ext hp] using ha
  · intro s hs
    exact position_eq_of_count_one u.val a.val hc p hp s hs.1

end SerrePositivity.EInfinity.IntervalCuts
