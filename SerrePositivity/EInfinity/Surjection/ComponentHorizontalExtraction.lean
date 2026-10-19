module

public import SerrePositivity.EInfinity.Surjection.OuterComponentExtraction
public import SerrePositivity.EInfinity.Surjection.HorizontalExtraction
public import SerrePositivity.EInfinity.TableReduction.IntervalVertices
public import SerrePositivity.EInfinity.TableReduction.ReductionPositionHead

/-!
# 元の二つの成功から得る最終除外前の水平合成成分

概要：Berger–Fresse §1.5.7 の指定値の出現で終わる外側成分を固定内側で合成して抽出する。
方針：成分終点の指定値の未除外性と内側の現在位置の先頭を元の成功から得る。
規約：最後の指定値より後の最終成分は別途扱う。
使われ方：水平・垂直の成分列を実際の合成表へ移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：指定値の出現で終わる元の外側成分の実際の水平合成抽出（BF §1.5.7）。
方針：元の二つの成功から行と先頭条件を得て、水平ブロック全体の転送を適用する。
規約：成分終点は第 i 出現で、その文字はまだ除外しない。
使われ方：最後の指定値の最終除外より前の水平成分を任意の後続へ接続する。 -/
lemma componentHorizontalExtraction_success {m n d e : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (s : Schedule (m + 1) d)
    (u : BasisWord (m + 1) d)
    (hu : reduceRows (rows w s) [] = some (List.ofFn u.val))
    (k : Fin (m + 1)) (i : Fin (occurrenceCount u.val k))
    (z : Fin (e + 1) → Equiv.Perm (Fin n)) (r : Schedule n e) (v : BasisWord n e)
    (hv : reduceRows (rows z r) [] = some (List.ofFn v.val)) (q : Fin (n + e))
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (compositionStateRemoved k
      (reductionRemoved w s u.val hu (occurrenceBoundaryPosition u.val k (by omega) (i.val + 1)))
      (reductionRemoved z r v.val hv q)) = some tail) :
    reduceRows
      (fixedInnerRows (z (reductionRow z r v.val hv q)) k
        (outerComponentExtraction w s u hu k (by omega) i.val).weightedVertices ++ rest)
      (compositionStateRemoved k
        (reductionRemoved w s u.val hu (occurrenceBoundaryPosition u.val k (by omega) i.val))
        (reductionRemoved z r v.val hv q)) =
      some ((outerComponentWord u.val k i.val).map (horizontalLabel k (v.val q)) ++ tail) := by
  obtain ⟨ys, hinner⟩ := reductionRemoved_available_head z r v.val hv q
  let p := occurrenceBoundaryPosition u.val k (by omega) (i.val + 1)
  have hp : p = occurrenceAt u.val k i := by
    apply Fin.ext
    exact occurrenceBoundary_at u.val k i
  have hvalue : u.val p = k := by
    rw [hp]
    exact occurrenceAt_value u.val k i
  have hnot := reductionRemoved_not_mem w s u.val hu p
  rw [hvalue] at hnot
  have houter : ExtractionPrefix
      (permutationRows (outerComponentExtraction w s u hu k (by omega) i.val).weightedVertices)
      (reductionRemoved w s u.val hu (occurrenceBoundaryPosition u.val k (by omega) i.val))
      (outerComponentExtraction w s u hu k (by omega) i.val).selected
      (reductionRemoved w s u.val hu p) := by
    rw [ReductionInterval.permutationRows_eq]
    exact (outerComponentExtraction w s u hu k (by omega) i.val).trace
  have hs := horizontalExtraction_success (z (reductionRow z r v.val hv q)) k
    (reductionRemoved z r v.val hv q) (v.val q) ys hinner _ _ _ _ houter hnot rest tail ht
  simpa only [outerComponentExtraction_word] using hs

end SerrePositivity.EInfinity.Surjection
