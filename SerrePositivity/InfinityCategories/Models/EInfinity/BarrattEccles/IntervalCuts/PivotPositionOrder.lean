module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RemainingActivePositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotInsertedOutput

/-!
模型。文献の定義との比較は後で
# 切断点色への挿入における内側位置の順序

概要：Berger–Fresse §2.2.6 の切断点色への挿入は前方残り位置と内側位置の二ブロックを作る。
方針：代入済み接頭語長と内側の相対番号を比較する。
規約：切断点色は非零性から一出現で、位置が存在する全 arity を扱う。
使われ方：合成活動集合と逆転数の二ブロック表示。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現挿入位置より前の残り位置は全内側位置より前（BF §2.2.6）。
方針：残り位置直後の接頭語長を挿入直前の長さで抑える。
規約：内側位置は任意であり非零切断点に限定しない。
使われ方：外側活動位置と内側活動列の交差順序。 -/
lemma compositeOuterPosition_lt_inner {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (p : Fin (m + 1 + d)) (hp : u.val p = k) (q : Fin (m + 1 + d))
    (hq : u.val q ≠ k) (hqp : q < p) (j : Fin (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r q hq < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp j := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_mono k (List.ofFn u.val) (r.segments v.val)
    (show q.val + 1 ≤ p.val from hqp)
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_non_slot k (List.ofFn u.val) (r.segments v.val)
    ⟨q.val, by simpa only [List.length_ofFn] using q.isLt⟩ (by
      simpa only [List.getElem_ofFn] using hq)
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (q.val + 1)) (r.segments v.val)).length =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take q.val) (r.segments v.val)).length + 1 at hs
  rw [hs] at H
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take q.val) (r.segments v.val)).length <
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val)).length + j.val
  omega

/-- 概要：挿入色が残り色より小さい条件は指定色が元の残り色より小さいこと（BF §2.2.6）。
方針：挿入色の範囲と残り色の番号公式を比較する。
規約：内側色の番号には依存しない。
使われ方：全内側活動位置に共通する交差逆転条件。 -/
lemma insertedPosition_lt_remaining_iff {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (c : {c : Fin (m + 1) // c ≠ k}) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b < _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k c ↔
      k < c.val := by
  simp only [Fin.lt_def, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition_val,
    _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_val, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingValue]
  have hck : c.val.val ≠ k.val := fun h => c.property (Fin.ext h)
  have := b.isLt
  split_ifs <;> omega

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：切断点色への挿入の内側位置写像（BF §2.2.6）。
方針：非零切断点色の一出現性を使い、既存の内側位置を取る。
規約：内側の切断点だけでなく全位置を送る。
使われ方：内側活動集合の合成語での像。 -/
def pivotInnerMap (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k)
    (j : Fin (n + e)) : Fin (m + n + (d + e)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k a.partition (by
    rw [← hp]; exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_pivot_eq_one u a.val.1 a.property.1) a.val.1 hp j

/-- 概要：内側位置写像は厳密順序を保存し反映（BF §2.2.6）。
方針：同じ接頭語長に相対位置を加える式を比較する。
規約：全内側位置。
使われ方：内側活動集合の単射性と逆転数の保存。 -/
lemma pivotInnerMap_lt_iff (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k)
    (i j : Fin (n + e)) : a.pivotInnerMap hp i < a.pivotInnerMap hp j ↔ i < j := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.pivotInnerMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition, Fin.lt_def]
  omega

/-- 概要：内側位置写像の合成語の文字は挿入色（BF §2.2.6）。
方針：一出現挿入の既存の文字評価を使う。
規約：正の内側 arity。
使われ方：内側活動位置の色と合成後の色の比較。 -/
lemma pivotInnerMap_value (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (j : Fin (n + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val (a.pivotInnerMap hp j) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k (v.val j) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_innerPosition u v k a.partition _ _ hp j hn

/-- 概要：内側の指定切断点は実際の合成切断点へ写る（BF §2.2.6）。
方針：切断点色分岐での合成位置の内側表示を使う。
規約：二段切断が保持する内側切断点を指定する。
使われ方：全内側活動位置の合成切断点以下の条件。 -/
lemma pivotInnerMap_at_cut (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k)
    (q : Fin (n + e)) (ha : a.val.2 = some q) :
    a.pivotInnerMap hp q = a.compositePosition := by
  exact (a.compositePosition_pivot_eq_inner q ha hp _).symm

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
