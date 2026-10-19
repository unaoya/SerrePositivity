module

public import SerrePositivity.EInfinity.IntervalCuts.NullaryRawCuts
public import SerrePositivity.EInfinity.IntervalCuts.NullaryRepeatedSlot
public import SerrePositivity.EInfinity.IntervalCuts.OutputListMembership

/-!
# 空語合成切断と二段切断の有限同値・全出力族

概要：Berger–Fresse §2.2.6 の nullary の二つの切断和を同じ有限添字へ移す。
方針：頂点分岐だけの二段切断を残り外側切断に移し、削除語の切断と対応させる。
規約：削除語が退化する場合も空の非零切断型として扱う。
使われ方：実際の左右辺の面テンソルと残る切断符号の比較。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：空語の二段切断は指定色以外の外側非零切断と同値（BF §2.2.6）。
方針：空の辺位置を排除し、一出現指定色の非辺分類で頂点分岐へ戻す。
規約：一出現性は空語分割から得る。
使われ方：nullary の二段切断を実際の削除語切断へ送る第一段階。 -/
def nullaryOuterCutEquiv {m d : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord 0 0)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) 0) :
    NestedEdgeCut u v k ≃
      {p : Fin (m + 1 + d) // EdgeNondegenerate u.val p ∧ u.val p ≠ k} where
  toFun a := ⟨a.val.1, a.property.1, a.nullary_pivot_ne_slot⟩
  invFun p := NestedEdgeCut.ofVertex p.val p.property.1
    ((edgeOutput_ne_edge_iff_single_nonpivot u p.val p.property.1 k).mpr
      ⟨p.property.2.symm, r.count_eq_one_of_empty⟩) rfl
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact a.nullary_eq_none.symm
  right_inv p := rfl

/-- 概要：空語合成の非零切断と実際の二段切断の有限同値（BF §2.2.6）。
方針：外側切断の表示を介して正規化前の削除語の非零切断へ移す。
規約：合成分割を明示的に指定し、退化する削除語も含む。
使われ方：nullary の左右の有限和の添字替え。 -/
def nullaryNestedCutEquiv {m d : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord 0 0)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) 0) :
    NestedEdgeCut u v k ≃
      {q : Fin (m + d) // EdgeNondegenerate (nullaryRawWord u v k r) q} :=
  (nullaryOuterCutEquiv u v k r).trans (nullaryRawCutEquiv u v k r)

/-- 概要：非零空語合成切断を持つ削除語を実際の基底語にする（BF §2.2.6）。
方針：語の全射性と切断非零性から隣接非退化性を得る。
規約：非零切断の存在しない退化語には適用しない。
使われ方：正規化生成元の各辺成分を面テンソルとして読む。 -/
def nullaryRawCutWord {m d : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord 0 0)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) 0)
    (q : {q : Fin (m + d) // EdgeNondegenerate (nullaryRawWord u v k r) q}) : BasisWord m d :=
  ⟨nullaryRawWord u v k r, nullaryRawWord_surjective u v k r,
    nondegenerate_of_edgeNondegenerate q.property⟩

/-- 概要：空語代入は残り色の出力頂点集合を保つ（BF §2.2.6）。
方針：左右の代入リストで残りラベルの所属を元の色の所属へ戻す。
規約：元の切断と削除語の非零性は要求しない。
使われ方：実際の面出力と活動色の比較。 -/
lemma nullaryRawWord_outputVertices {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) (p : Fin (m + 1 + d))
    (hp : u.val p ≠ k) (a : {a : Fin (m + 1) // a ≠ k}) :
    edgeOutputVertices (nullaryRawWord u v k r) (compositeOuterPosition u v k r p hp)
      (BarrattEccles.remainingPosition m 0 k a) = edgeOutputVertices u.val p a.val := by
  apply edgeOutputVertices_eq_of_list_membership
  · rw [nullaryRawWord_prefix]
    exact remaining_mem_substitute_iff k a _ _
  · rw [nullaryRawWord_suffix]
    exact remaining_mem_substitute_iff k a _ _

/-- 概要：対応した空語合成切断の全出力族は二段切断の出力族（BF §2.2.6）。
方針：全出力ラベルを残り色に分解して出力頂点集合の一致を使う。
規約：出力 arity 零を含み、削除語全体の非退化性は仮定しない。
使われ方：nullary の実際の左右辺の面テンソルの一致。 -/
lemma nullaryNestedCutEquiv_outputFamily {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) (a : NestedEdgeCut u v k) :
    edgeOutput (nullaryRawCutWord u v k r (nullaryNestedCutEquiv u v k r a))
      (nullaryNestedCutEquiv u v k r a).val = a.outputFamily := by
  funext j
  unfold NestedEdgeCut.outputFamily
  cases hj : operadInsertionEquiv m 0 k j with
  | inl b =>
    have he : j = BarrattEccles.remainingPosition m 0 k b := by
      have H := congrArg (operadInsertionEquiv m 0 k).symm hj
      simpa only [Equiv.symm_apply_apply, BarrattEccles.remainingPosition] using H
    apply Subtype.ext
    change edgeOutputVertices (nullaryRawWord u v k r)
      (compositeOuterPosition u v k r a.val.1 a.nullary_pivot_ne_slot) j =
        edgeOutputVertices u.val a.val.1 b.val
    rw [he]
    exact nullaryRawWord_outputVertices u v k r a.val.1 _ b
  | inr b => exact Fin.elim0 b

/-- 概要：空語合成切断の各残り色出力は元の外側出力（BF §2.2.6）。
方針：出力頂点集合の一致を面の部分型へ戻す。
規約：正規化前の非零切断から得た基底語を使う。
使われ方：空語代入後の活動位置と逆転数を比較する。 -/
lemma nullaryNestedCutEquiv_remaining_output {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) (a : NestedEdgeCut u v k)
    (b : {b : Fin (m + 1) // b ≠ k}) :
    edgeOutput (nullaryRawCutWord u v k r (nullaryNestedCutEquiv u v k r a))
      (nullaryNestedCutEquiv u v k r a).val (BarrattEccles.remainingPosition m 0 k b) =
        edgeOutput u a.val.1 b.val :=
  Subtype.ext (nullaryRawWord_outputVertices u v k r a.val.1 a.nullary_pivot_ne_slot b)

end SerrePositivity.EInfinity.IntervalCuts
