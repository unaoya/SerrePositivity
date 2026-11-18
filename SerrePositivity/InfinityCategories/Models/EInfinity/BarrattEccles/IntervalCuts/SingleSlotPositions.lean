module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionCutPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWordOccurrence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceCompleteness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSingle

/-!
模型。文献の定義との比較は後で
# 一出現の指定色への挿入語の位置

概要：Berger–Fresse §2.2.6 の切断点色への一出現挿入で、内側位置を実際の合成語へ移す。
方針：唯一分割の全語部分を接頭語の直後へ置き、その長さで有限位置と値を計算する。
規約：元の語の指定色は一出現。内側位置が存在する範囲で全 arity を扱う。
使われ方：二段切断の切断点色分岐の順方向写像。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現の色の全列挙位置はその唯一の実際の位置（BF §1.2.4）。
方針：出現の完全列挙と一元の有限添字の一意性を使う。
規約：全射性や非退化性は不要。
使われ方：合成語の出現番号による分解を元の指定位置へ戻す。 -/
lemma occurrenceAt_of_count_one {n l : ℕ} (u : Fin l → Fin n) (k : Fin n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k = 1) (p : Fin l) (hp : u p = k)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u k j = p := by
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete u k p hp
  have hij : j = i := by
    apply Fin.ext
    have hb0 := i.isLt
    have hb1 := j.isLt
    omega
  rwa [hij]

/-- 概要：分割数が一なら指定した部分語は全語（BF §1.2.4）。
方針：分割数を一へ移して唯一分割の評価を使う。
規約：元の語長は零も含む。
使われ方：一出現挿入の中央部分を内側語全体へ同定する。 -/
lemma segment_of_count_one {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hc : t = 1)
    {α : Type*} (v : Fin l → α) (j : Fin t) : r.segment v j = List.ofFn v := by
  subst t
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hj, r.eq_single]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single_segment v

/-- 概要：分割数が一なら全部分語列は全語だけの一項列（BF §1.2.4）。
方針：唯一分割の成分を有限列の再帰式で評価する。
規約：空語の唯一分割も含む。
使われ方：一出現の後に消費済みとなる部分語列を除く。 -/
lemma segments_of_count_one {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hc : t = 1)
    {α : Type*} (v : Fin l → α) : r.segments v = [List.ofFn v] := by
  subst t
  rw [r.eq_single]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.ofFn_succ, List.ofFn_zero,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single_segment]

/-- 概要：一出現挿入の合成語は接頭語・内側全語・接尾語に分かれる（BF §2.2.6）。
方針：唯一の出現番号を実際の位置に同定し、全語の一部分割を評価する。
規約：挿入位置の前後の元の語の順序を保つ。
使われ方：切断点色への挿入位置の範囲と値の計算。 -/
lemma compositeWord_at_single_slot {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (p : Fin (m + 1 + d)) (hp : u.val p = k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val) ++
        (List.ofFn v.val).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop (p.val + 1)) [] := by
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨0, by omega⟩
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_at_occurrence u v k r j
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceAt_of_count_one u.val k hc p hp j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_of_count_one r hc v.val j] at H
  simpa only [j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segments_of_count_one r hc, List.drop_succ_cons, List.drop_zero] using H

/-- 概要：一出現の指定色へ挿入した内側位置の合成語での有限位置（BF §2.2.6）。
方針：代入済み接頭語の長さに内側位置を加える。
規約：外側指定色は一出現、内側語次数は任意。
使われ方：切断点色へ挿入する二段切断の合成切断点。 -/
def compositeInnerPosition {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) : Fin (m + n + (d + e)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val)).length + q.val, by
    have hl := congrArg List.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length] at hl
    simp only [List.length_append, List.length_map, List.length_ofFn] at hl
    have hq := q.isLt
    omega⟩

/-- 概要：一出現の内側位置の文字は元の挿入ラベル（BF §2.2.6）。
方針：接頭語の長さを引き、内側全語の同じ位置を評価する。
規約：有限位置の範囲証明は既存の長さ公式から得る。
使われ方：切断点色を内側の実際の出力色へ移す。 -/
lemma compositeInnerPosition_value {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (p : Fin (m + 1 + d)) (hp : u.val p = k) (q : Fin (n + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q).val]'(by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q).isLt) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k (v.val q) := by
  have hq : q.val < ((List.ofFn v.val).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)).length := by
    simpa only [List.length_map, List.length_ofFn] using q.isLt
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition,
    List.append_assoc, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_append_left hq, List.getElem_map, List.getElem_ofFn]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
