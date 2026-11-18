module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotPositionOrder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TwoBlockInsertedOutput

/-!
模型。文献の定義との比較は後で
# 二出現色への挿入の最初の部分語

概要：Berger–Fresse §2.2.6 の二出現色への内側辺作用で全内側活動位置を第一部分語へ送る。
方針：標準二部分割の第一長が切断点番号+1 であることを使う。
規約：内側切断点以下で位置写像を定義し、他の位置の値は比較に使わない。
使われ方：二出現色分岐の合成活動集合と逆転数の比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

private lemma firstLength_cast {t l : ℕ} (hc : t = 2) (ht : 0 < t)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) :
    ((cast (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition a l) hc) r).val 0).val =
      (r.val ⟨0, ht⟩).val := by
  cases hc
  rfl

/-- 概要：二出現分岐の第一部分語の長さは内側切断点番号+1（BF §2.2.6）。
方針：分割を標準二部分割へ移し、第一成分を評価する。
規約：元の出現数における零番号を保持する。
使われ方：全内側活動位置が第一部分語に入ること。 -/
lemma nonpivot_first_length (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    (a.partition.val ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩).val = q.val + 1 := by
  have hc := a.occurrenceCount_eq_two_of_some_nonpivot q ha hp.symm
  have H := congrArg (fun r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 (n + e) => (r.val 0).val)
    (a.partition_of_some_nonpivot q ha hp.symm)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.firstLength_cast hc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k)] at H
  exact H

/-- 概要：二出現分岐の最初の指定出現は区切りである（BF §2.2.3）。
方針：二番目の出現を厳密に後の同色位置として取る。
規約：位置は既存の occurrenceAt の零番号。
使われ方：外側活動集合から置換対象の一位置を除く。 -/
lemma nonpivot_first_caesura (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩) := by
  have hc := a.occurrenceCount_eq_two_of_some_nonpivot q ha hp.symm
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨1, by omega⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u.val k (by
    change 0 < 1; omega), ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k j,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩]

/-- 概要：最初の指定出現は外側活動位置である（BF §2.2.3）。
方針：最初の指定出現が区切りであることを活動集合へ入れる。
規約：内側辺作用の二出現分岐。
使われ方：削除後の外側活動集合の個数と順位。 -/
lemma nonpivot_first_mem_active (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩ ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1 :=
  Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, a.nonpivot_first_caesura q ha hp⟩))

/-- 概要：内側切断点以下を最初の指定出現の部分語位置へ送る（BF §2.2.6）。
方針：切断点以下では第一部分語の同じ相対番号を使い、それ以外では合成切断点を返す。
規約：活動集合に属する全位置は切断点以下。
使われ方：内側活動集合の合成語における像。 -/
def nonpivotInnerMap (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (j : Fin (n + e)) :
    Fin (m + n + (d + e)) :=
  if hj : j ≤ q then
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition u v k a.partition ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩
      ⟨j.val, by rw [a.nonpivot_first_length q ha hp]; omega⟩
  else a.compositePosition

/-- 概要：内側切断点以下の位置は共通の接頭語長だけずれる（BF §2.2.6）。
方針：第一部分語への位置写像の番号を評価する。
規約：指定位置が切断点以下であることを明示する。
使われ方：内側位置と前後の外側位置の厳密順序。 -/
lemma nonpivotInnerMap_val (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (j : Fin (n + e)) (hj : j ≤ q) :
    (a.nonpivotInnerMap q ha hp j).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩).val)
          (a.partition.segments v.val)).length + j.val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nonpivotInnerMap, dite_eq_left hj, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition]

/-- 概要：第一部分語へ送った内側位置の合成色は元の挿入色（BF §2.2.6）。
方針：一般の部分語位置の文字評価と第一部分語の開始位置零を使う。
規約：正の内側 arity、切断点以下の位置。
使われ方：内側活動像の色順と出力辺の比較。 -/
lemma nonpivotInnerMap_value (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (j : Fin (n + e)) (hj : j ≤ q) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val (a.nonpivotInnerMap q ha hp j) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k (v.val j) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nonpivotInnerMap, dite_eq_left hj, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentPosition_value]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.start_zero, Nat.zero_add]

/-- 概要：内側切断点以下では位置の厳密順序を保持し反映（BF §2.2.6）。
方針：同じ前置長を加える番号式を比較する。
規約：比較する両位置とも切断点以下。
使われ方：内側活動集合上の単射性と内部逆転数。 -/
lemma nonpivotInnerMap_lt_iff (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (i j : Fin (n + e))
    (hi : i ≤ q) (hj : j ≤ q) :
    a.nonpivotInnerMap q ha hp i < a.nonpivotInnerMap q ha hp j ↔ i < j := by
  change (a.nonpivotInnerMap q ha hp i).val < (a.nonpivotInnerMap q ha hp j).val ↔ i.val < j.val
  rw [a.nonpivotInnerMap_val q ha hp i hi, a.nonpivotInnerMap_val q ha hp j hj]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
