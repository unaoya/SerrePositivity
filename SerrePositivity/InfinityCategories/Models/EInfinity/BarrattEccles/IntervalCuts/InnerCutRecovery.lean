module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SegmentCutRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TwoPiecePartitions

/-!
模型。文献の定義との比較は後で
# 残りラベル切断点からの内側条件の復元

概要：Berger–Fresse §2.2.6 の残りラベル分岐で内側作用の非零条件を回収する。
方針：一部分語は切断点の片側に、二部分語は共有端点の跨ぎによって左右に収まる。
規約：一部分割では次数零、二部分割では共有位置の非零辺切断を得る。
使われ方：二段切断への有限対応の全射性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：分割数の等式で移した部分語は同じ有限位置なら元と一致（BF §1.2.4）。
方針：分割数の等式を消去し、位置の外延性を使う。
規約：値の型は任意。
使われ方：二部分割の共有位置の非零性を元の分割の各 Nodup から戻す。 -/
lemma segment_cast_count {t s l : ℕ} (h : t = s) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    {α : Type*} (v : Fin l → α) (i : Fin t) (j : Fin s) (hij : i.val = j.val) :
    (cast (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition a l) h) r).segment v j = r.segment v i := by
  cases h
  have he : j = i := Fin.ext hij.symm
  subst j
  rfl

/-- 概要：指定色二出現の非零合成切断では内側共有位置の切断も非零（BF §2.2.6）。
方針：共有端点の前後にある二部分語の Nodup を、標準二部分割の take・drop へ移す。
規約：元の分割を二部分割へ移送して得る共有位置を使う。
使われ方：逆対応の内側辺入力分岐の非退化性。 -/
lemma inner_two_cut_nondegenerate_of_composite {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2) (q : Fin (m + n + (d + e)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut (by omega)
      (cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e)) hc) r)) := by
  let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨1, by omega⟩
  let r' := cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e)) hc) r
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegment_boundary_straddles u v k r hn q h i j rfl
  have hL := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_nodup_of_last_le_cut u v k r hn q h i H.1.le
  have hR := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_nodup_of_cut_le_first u v k r hn q h j H.2.le
  have hL' : (r'.segment v.val 0).Nodup := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_cast_count hc r v.val i 0 rfl]
    exact hL
  have hR' : (r'.segment v.val 1).Nodup := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_cast_count hc r v.val j 1 rfl]
    exact hR
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_twoCut (show 0 < n + e by omega) r'
  rw [← hr, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_segment_zero] at hL'
  rw [← hr, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_segment_one] at hR'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup v.val _ hL' hR'

/-- 概要：一出現挿入の残り位置に非零合成切断があれば内側次数は零（BF §2.2.6）。
方針：唯一の挿入部分語は切断点の片側にあり、全内側語が Nodup となる。
規約：切断点は指定色以外の外側位置にある。
使われ方：逆対応の内側頂点入力分岐の次数条件。 -/
lemma inner_degree_zero_of_single_slot_outer_cut {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p ≠ k)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp)) : e = 0 := by
  let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨0, by omega⟩
  have hN : (r.segment v.val i).Nodup := by
    rcases lt_trichotomy p (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i) with hpi | he | hip
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_nodup_of_cut_le_first u v k r hn _ h i
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt_segmentFirst u v k r hn p hp i hpi).le
    · exact False.elim (hp (he ▸ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k i))
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_nodup_of_last_le_cut u v k r hn _ h i
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeSegmentLast_lt_outerPosition u v k r hn p hp i hip).le
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segment_of_count_one r hc] at hN
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexNondegenerate_iff v).mp (List.nodup_ofFn.mp hN)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
