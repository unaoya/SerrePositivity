module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCut
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutPositions

/-!
模型。文献の定義との比較は後で
# 二段切断の合成切断の全分岐の非退化性

概要：Berger–Fresse §2.2.6 の二段切断を、実際の合成基底語の非零切断へ送る。
方針：非切断点色の一部分割・二部分割で各部分語の重複消滅を証明し、既存の切断点色分岐と結ぶ。
規約：合成基底語を使う正の内側 arity を扱う。nullary は別途扱う。
使われ方：二段切断と非零合成切断の有限対応の順方向写像。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：分割数の等式による移送は実際の部分語列を変えない（BF §1.2.4）。
方針：個数の等式を消去する。
規約：元の語長と文字列は固定する。
使われ方：二段切断の二部分割を標準の二分割へ戻す。 -/
lemma segments_cast_count {t t' l : ℕ} (h : t = t') (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    {α : Type*} (v : Fin l → α) :
    (cast (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition a l) h) r).segments v = r.segments v := by
  subst t'
  rfl

/-- 概要：内側の非零辺切断による二部分割の各部分語は重複を持たない（BF §2.2.6）。
方針：二分割を共有位置を含む接頭語と接尾語に評価する。
規約：二つの部分語は同じ共有文字をそれぞれ一回含む。
使われ方：非切断点色の二出現分岐の代入条件。 -/
lemma two_partition_segments_nodup {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (q : Fin (n + e))
    (hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q) :
    ∀ part ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).segments v.val, part.Nodup := by
  intro part hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  fin_cases i
  · change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).segment v.val 0).Nodup
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_segment_zero q v.val]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup v.val q hq
  · change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).segment v.val 1).Nodup
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_segment_one q v.val]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup v.val q hq

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：非切断点色の内側辺切断から選んだ分割は標準の二部分割（BF §1.2.4・§2.2.6）。
方針：分割の構成を評価して二出現の個数移送を打ち消す。
規約：内側切断点を固定する。
使われ方：選んだ分割の全部分語を実際の二つの切断語へ同定する。 -/
lemma partition_of_some_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hk : k ≠ u.val a.val.1) :
    cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e))
      (a.occurrenceCount_eq_two_of_some_nonpivot q ha hk)) a.partition =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => cases ha
  | some s =>
    cases ha
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition, hk]

/-- 概要：非切断点色分岐で選んだ合成分割の全部分語は重複を持たない（BF §2.2.6）。
方針：頂点分岐では零次数の全射語の単射性、辺分岐では非零辺切断の左右を使う。
規約：頂点の一出現と辺の二出現を同じ条件で扱う。
使われ方：非切断点色分岐の合成切断の非退化性の供給。 -/
lemma partition_segments_nodup_of_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (hk : u.val a.val.1 ≠ k) : ∀ part ∈ a.partition.segments v.val, part.Nodup := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none =>
    have he : e = 0 := h.2.2
    cases he
    have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 :=
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_ne_edge_iff_single_nonpivot u p h.1 k).mp h.2.1).2
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segments_of_count_one _ hc]
    intro part hp
    have hp' := List.mem_singleton.mp hp
    subst part
    exact List.nodup_ofFn_ofInjective (Finite.injective_iff_surjective.mpr v.surjective)
  | some q =>
    let a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k := ⟨(p, some q), h⟩
    have H := congrArg (fun r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 (n + e) => r.segments v.val)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition_of_some_nonpivot a q rfl hk.symm)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.segments_cast_count (a.occurrenceCount_eq_two_of_some_nonpivot q rfl hk.symm)
      a.partition v.val] at H
    rw [H]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.two_partition_segments_nodup v q h.2.2

/-- 概要：非切断点色分岐の合成位置は実際に非零切断となる（BF §2.2.6）。
方針：各部分語の重複消滅を指定色以外の切断点を保つ一般代入補題へ渡す。
規約：実際の合成基底語と構成済みの位置を使う。
使われ方：順方向写像の残りの二分岐を非零切断へ持ち上げる。 -/
lemma compositePosition_nonpivot_nondegenerate (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hk : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition_segments_nodup_of_nonpivot a hk
  rcases a with ⟨⟨p, q⟩, h⟩
  cases q with
  | none => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.composite_non_slot_cut_nondegenerate _ _ _ _ hn _ hk h.1 hr
  | some q =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_right hk]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.composite_non_slot_cut_nondegenerate _ _ _ _ hn _ hk h.1 hr

/-- 概要：二段切断から選んだ合成位置は全分岐で非零切断となる（BF §2.2.6）。
方針：切断点色との一致で分け、頂点入力が切断点色になりえないことを使う。
規約：正の内側 arity、任意の語次数。
使われ方：分割と位置の対を非零合成切断の有限添字へ送る。 -/
lemma compositePosition_nondegenerate (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  by_cases hk : u.val a.val.1 = k
  · cases ha : a.val.2 with
    | none =>
      have H := a.property.2
      rw [ha] at H
      exact False.elim (H.1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u a.val.1 a.property.1 k).mpr
        ⟨a.val.1, Finset.mem_insert_self _ _, hk⟩))
    | some q => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_nondegenerate a hn q ha hk
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_nondegenerate a hn hk

end NestedEdgeCut

/-- 概要：実際の合成基底語の非零辺切断の全有限添字（BF §1.2.4・§2.2.6）。
方針：重なる分割とその合成語の有限切断点の対に非退化性を課す。
規約：正の内側 arity を固定して合成基底語を使う。
使われ方：二段切断との有限全単射の左側の添字。 -/
abbrev CompositeEdgeCut {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (hn : 0 < n) :=
  {a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e) × Fin (m + n + (d + e)) //
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.1 hn).val a.2}

/-- 概要：二段切断を実際の非零合成切断へ送る写像（BF §2.2.6）。
方針：構成した分割と合成位置を、全分岐の非退化性で部分型へ持ち上げる。
規約：同じ既存の合成・切断の添字を使う。
使われ方：部分合成則の有限和対応の順方向写像。 -/
def _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.toCompositeCut {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)} (hn : 0 < n) (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn :=
  ⟨(a.partition, a.compositePosition), a.compositePosition_nondegenerate hn⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
