module

public import SerrePositivity.EInfinity.Surjection.OuterComponentExtraction
public import SerrePositivity.EInfinity.Surjection.SingletonHorizontalExtraction
public import SerrePositivity.EInfinity.TableReduction.IntervalVertices
public import SerrePositivity.EInfinity.TableReduction.LastReductionState

/-!
# 元の内側最終位置での最後の外側成分の合成抽出

概要：Berger–Fresse §1.5.7 の最後の指定値より後の水平成分を元の二つの成功から構成する。
方針：元の内側最終状態の一文字可用行を最終水平ブロック転送へ渡す。
規約：外側指定値の最終除外を許し、元の後続状態を保つ。
使われ方：水平・垂直の成分列の最後の水平部分を閉じる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：内側最終状態で最後の外側成分を実際の合成行列へ転送（BF §1.5.7）。
方針：元の二つの成功から内側一文字状態と外側成分の元の証跡を得る。
規約：行表示・一文字可用性・成分成功を別途仮定しない。
使われ方：最後の水平成分を任意の後続合成抽出へ接続する。 -/
lemma finalHorizontalExtraction_success {m n d e : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (s : Schedule (m + 1) d)
    (u : BasisWord (m + 1) d)
    (hu : reduceRows (rows w s) [] = some (List.ofFn u.val)) (k : Fin (m + 1))
    (z : Fin (e + 1) → Equiv.Perm (Fin n)) (r : Schedule n e) (v : BasisWord n e)
    (hv : reduceRows (rows z r) [] = some (List.ofFn v.val))
    (q : Fin (n + e)) (hq : q.val + 1 = n + e)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (compositionStateRemoved k
      (reductionRemoved w s u.val hu
        (occurrenceBoundaryPosition u.val k (by omega) (occurrenceCount u.val k + 1)))
      (reductionRemoved z r v.val hv q)) = some tail) :
    reduceRows
      (fixedInnerRows (z (reductionRow z r v.val hv q)) k
        (outerComponentExtraction w s u hu k
          (by omega) (occurrenceCount u.val k)).weightedVertices ++
        rest)
      (compositionStateRemoved k
        (reductionRemoved w s u.val hu
          (occurrenceBoundaryPosition u.val k (by omega) (occurrenceCount u.val k)))
        (reductionRemoved z r v.val hv q)) =
      some ((outerComponentWord u.val k (occurrenceCount u.val k)).map
        (horizontalLabel k (v.val q)) ++ tail) := by
  have hinner := reductionRemoved_last_singleton z r v hv q hq
  have houter : ExtractionPrefix
      (permutationRows
        (outerComponentExtraction w s u hu k (by omega) (occurrenceCount u.val k)).weightedVertices)
      (reductionRemoved w s u.val hu
        (occurrenceBoundaryPosition u.val k (by omega) (occurrenceCount u.val k)))
      (outerComponentExtraction w s u hu k (by omega) (occurrenceCount u.val k)).selected
      (reductionRemoved w s u.val hu
        (occurrenceBoundaryPosition u.val k (by omega) (occurrenceCount u.val k + 1))) := by
    rw [ReductionInterval.permutationRows_eq]
    exact (outerComponentExtraction w s u hu k (by omega) (occurrenceCount u.val k)).trace
  have hs := singletonHorizontalExtraction_success (z (reductionRow z r v.val hv q)) k
    (reductionRemoved z r v.val hv q) (v.val q) hinner _ _ _ _ houter rest tail ht
  simpa only [outerComponentExtraction_word] using hs

end SerrePositivity.EInfinity.Surjection
