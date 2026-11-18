module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterComponentExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionPositionHead

/-!
模型。文献の定義との比較は後で
# 元の二つの成功から得る最終除外前の水平合成成分

概要：Berger–Fresse §1.5.7 の指定値の出現で終わる外側成分を固定内側で合成して抽出する。
方針：成分終点の指定値の未除外性と内側の現在位置の先頭を元の成功から得る。
規約：最後の指定値より後の最終成分は別途扱う。
使われ方：水平・垂直の成分列を実際の合成表へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値の出現で終わる元の外側成分の実際の水平合成抽出（BF §1.5.7）。
方針：元の二つの成功から行と先頭条件を得て、水平ブロック全体の転送を適用する。
規約：成分終点は第 i 出現で、その文字はまだ除外しない。
使われ方：最後の指定値の最終除外より前の水平成分を任意の後続へ接続する。 -/
lemma componentHorizontalExtraction_success {m n d e : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (hu : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn u.val))
    (k : Fin (m + 1)) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (z : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows z r) [] = some (List.ofFn v.val)) (q : Fin (n + e))
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition u.val k (by omega) (i.val + 1)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv q)) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows (z (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow z r v.val hv q)) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s u hu k (by omega) i.val).weightedVertices ++ rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition u.val k (by omega) i.val))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv q)) =
      some ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord u.val k i.val).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k (v.val q)) ++ tail) := by
  obtain ⟨ys, hinner⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved_available_head z r v.val hv q
  let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition u.val k (by omega) (i.val + 1)
  have hp : p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i := by
    apply Fin.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_at u.val k i
  have hvalue : u.val p = k := by
    rw [hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k i
  have hnot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved_not_mem w s u.val hu p
  rw [hvalue] at hnot
  have houter : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s u hu k (by omega) i.val).weightedVertices)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition u.val k (by omega) i.val))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s u hu k (by omega) i.val).selected
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu p) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.permutationRows_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction w s u hu k (by omega) i.val).trace
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalExtraction_success (z (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow z r v.val hv q)) k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv q) (v.val q) ys hinner _ _ _ _ houter hnot rest tail ht
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction_word] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
