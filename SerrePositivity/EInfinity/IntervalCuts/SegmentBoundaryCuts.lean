module

public import SerrePositivity.EInfinity.IntervalCuts.SegmentPositions
public import SerrePositivity.EInfinity.IntervalCuts.CutConvexity
public import SerrePositivity.EInfinity.Surjection.OverlapCoverage

/-!
# 共有端点の二出現による合成切断の制約

概要：Berger–Fresse §2.2.6 の共有端点は合成語の異なる二位置に同じ色として現れる。
方針：各部分語の位置の順序と非零切断の厳密な跨ぎ条件を使う。
規約：正の内側 arity により各部分語は非空。
使われ方：非零合成切断では外側指定色が高々二回であること。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：挿入部分語の先頭の実際の合成位置（BF §2.2.6）。
方針：正長な部分語の零番目を合成語へ送る。
規約：正の内側 arity を使う。
使われ方：共有端点の後の出現。 -/
def compositeSegmentFirst {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (i : Fin (occurrenceCount u.val k)) : Fin (m + n + (d + e)) :=
  compositeSegmentPosition u v k r i ⟨0, by have := r.positive (by omega) i; omega⟩

/-- 概要：挿入部分語の末尾の実際の合成位置（BF §2.2.6）。
方針：正長な部分語の長さ引く一の位置を合成語へ送る。
規約：長さ一の部分語では先頭と一致する。
使われ方：共有端点の前の出現。 -/
def compositeSegmentLast {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (i : Fin (occurrenceCount u.val k)) : Fin (m + n + (d + e)) :=
  compositeSegmentPosition u v k r i
    ⟨(r.val i).val - 1, by have := r.positive (by omega) i; omega⟩

/-- 概要：隣接部分語の末尾と先頭の合成値は一致する（BF §2.2.6）。
方針：二つの合成値を元の内側位置へ戻し、分割の共有端点を使う。
規約：部分語番号は一つ違う。
使われ方：同色二位置の厳密な跨ぎ条件の入力。 -/
lemma compositeSegment_boundary_value {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (i j : Fin (occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    (compositeBasisWord u v k r hn).val (compositeSegmentLast u v k r hn i) =
      (compositeBasisWord u v k r hn).val (compositeSegmentFirst u v k r hn j) := by
  simp only [compositeSegmentLast, compositeSegmentFirst, compositeSegmentPosition_value]
  apply congrArg (BarrattEccles.insertedPosition m n k)
  apply congrArg v.val
  apply Fin.ext
  simpa only [Nat.add_zero] using (r.start_next i j hij).symm

/-- 概要：非零合成切断点は各共有端点の二出現の間に厳密に入る（BF §2.2.6）。
方針：前部分語の末尾は次の先頭より前で、両位置の色は同じ。
規約：二つの共有位置自身で切ることはできない。
使われ方：三部分語以上の合成には非零辺切断が存在しないこと。 -/
lemma compositeSegment_boundary_straddles {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (i j : Fin (occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    compositeSegmentLast u v k r hn i < q ∧ q < compositeSegmentFirst u v k r hn j := by
  apply repeated_straddles h
  · apply compositeSegmentPosition_lt
    change i.val < j.val
    omega
  · exact compositeSegment_boundary_value u v k r hn i j hij

/-- 概要：非零合成切断があれば外側指定色の出現数は高々二（BF §2.2.6）。
方針：三部分語の二共有端点を跨ぐと、中央部分語の先頭より前かつ末尾より後となり矛盾。
規約：外側切断の非零性を仮定せず、任意の合成分割を扱う。
使われ方：逆対応の分割を一部分または二部分に限定する。 -/
lemma slot_occurrenceCount_le_two_of_composite_cut {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q) :
    occurrenceCount u.val k ≤ 2 := by
  by_contra hc
  let i : Fin (occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (occurrenceCount u.val k) := ⟨1, by omega⟩
  let s : Fin (occurrenceCount u.val k) := ⟨2, by omega⟩
  have H := compositeSegment_boundary_straddles u v k r hn q h i j rfl
  have K := compositeSegment_boundary_straddles u v k r hn q h j s rfl
  have hj : compositeSegmentFirst u v k r hn j ≤ compositeSegmentLast u v k r hn j := by
    change _ + 0 ≤ _ + ((r.val j).val - 1)
    omega
  exact (not_lt_of_ge hj) (lt_trans K.1 H.2)

end SerrePositivity.EInfinity.IntervalCuts
