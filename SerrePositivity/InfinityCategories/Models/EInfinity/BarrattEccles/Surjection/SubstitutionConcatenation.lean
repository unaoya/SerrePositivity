module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrencePrefixCounts

/-!
模型。文献の定義との比較は後で
# 出現順の代入と外側語の連結

概要：Berger–Fresse §1.2.4・§1.5.7 の代入を外側の成分境界で分解する。
方針：前半の指定値の出現回数だけ内側部分語を消費する。
規約：部分語不足や空部分語も元の代入と同じ意味で扱う。
使われ方：融合表の成分語列と実際の compositeWord を比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：外側語の連結への代入は消費済み部分語を除いた後半への代入と連結（BF §1.5.7）。
方針：前半で帰納し、指定値の場合だけ内側列を一つ進める。
規約：部分語数一致の仮定は不要。
使われ方：元の外側語を出現境界で切り、成分語列と照合する。 -/
lemma substitute_append {m n : ℕ} (k : Fin (m + 1))
    (left right : List (Fin (m + 1))) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (left ++ right) parts =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k left parts ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k right (parts.drop (left.count k)) := by
  induction left generalizing parts with
  | nil => simp only [List.nil_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.count_nil, List.drop_zero]
  | cons a left ih =>
    by_cases ha : a = k
    · subst a
      cases parts <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, ih, List.drop_succ_cons, List.append_assoc]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, ha, ih]

/-- 概要：第 j 出現での代入を前半・挿入語・後半へ厳密に分解（BF §1.5.7）。
方針：その出現で元の語を分割し、前半の出現回数を j に戻す。
規約：内側部分語が不足する場合も同じ分解が成立する。
使われ方：融合表の各垂直語と同じ出現に代入した部分語を照合する。 -/
lemma substitute_at_occurrence {m n l : ℕ} (v : Fin l → Fin (m + 1)) (k : Fin (m + 1))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn v) parts =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val) parts ++
        ((parts.drop j.val).headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1))
            (parts.drop (j.val + 1)) := by
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val < (List.ofFn v).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).isLt
  have hv : (List.ofFn v)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val] = k := by
    simpa only [List.getElem_ofFn] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value v k j
  have hs : (List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val ++
      k :: (List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1) = List.ofFn v := by
    calc
      _ = (List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val ++
          (List.ofFn v)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val] ::
            (List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1) := by rw [hv]
      _ = List.ofFn v := by rw [List.getElem_cons_drop hp, List.take_append_drop]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append k ((List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val)
    (k :: (List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1)) parts
  rw [hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_count_take] at h
  have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (k :: (List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1))
      (parts.drop j.val) =
      ((parts.drop j.val).headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1))
          (parts.drop (j.val + 1)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.tail_drop]
  rw [hc] at h
  simpa only [List.append_assoc] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
