module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutValidity

/-!
模型。文献の定義との比較は後で
# 二段切断から非零合成切断への写像の単射性

概要：Berger–Fresse §2.2.6 の順方向の対応から元の二段切断が一意に決まることを示す。
方針：切断点ラベルで外側位置を戻し、内側位置は合成位置または二部分割から戻す。
規約：正の内側 arity と既存の実際の合成基底語を使う。
使われ方：二段切断と非零合成切断の有限全単射の単射側。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：外側切断点の色へ作用する二段切断は内側辺切断点を持つ（BF §2.2.6）。
方針：切断点色の出力は辺なので頂点入力の none 分岐を排除する。
規約：内側 arity の正性を追加せず存在を示す。
使われ方：切断点ラベルの比較で内側切断点を取り出す。 -/
lemma exists_some_of_pivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k) :
    ∃ q, a.val.2 = some q := by
  cases ha : a.val.2 with
  | none =>
    have H := a.property.2
    rw [ha] at H
    exact False.elim (H.1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u a.val.1 a.property.1 k).mpr
      ⟨a.val.1, Finset.mem_insert_self _ _, hp⟩))
  | some q => exact ⟨q, rfl⟩

/-- 概要：切断点色分岐の合成位置は接頭語長と内側切断点の和（BF §2.2.6）。
方針：合成位置の分岐と一出現挿入位置の構成を評価する。
規約：有限位置の自然数値で述べる。
使われ方：同じ分割と外側位置から内側切断点を一意に復元する。 -/
lemma compositePosition_pivot_val (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    a.compositePosition.val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take a.val.1.val) (a.partition.segments v.val)).length +
        q.val := by
  rcases a with ⟨⟨p, s⟩, h⟩
  cases s with
  | none => cases ha
  | some s =>
    cases ha
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition, dite_eq_left hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition]

/-- 概要：同じ非零合成切断を与える二段切断の外側位置は等しい（BF §2.2.6）。
方針：残りラベルと挿入ラベルの非交差、残りラベルの単射性、切断点色の一意性を使う。
規約：合成分割と合成位置をともに比較する。
使われ方：有限対応の単射性の外側成分。 -/
lemma toCompositeCut_outer_injective (hn : 0 < n) (a b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (h : a.toCompositeCut hn = b.toCompositeCut hn) : a.val.1 = b.val.1 := by
  have hr := congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn => x.val.1) h
  have hq := congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn => x.val.2) h
  change a.partition = b.partition at hr
  change a.compositePosition = b.compositePosition at hq
  have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k b.partition hn).val b.compositePosition := by rw [hr, hq]
  by_cases ha : u.val a.val.1 = k <;> by_cases hb : u.val b.val.1 = k
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique a.property.1 b.val.1 (hb.trans ha.symm)).symm
  · obtain ⟨q, hqa⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.exists_some_of_pivot a ha
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_value a hn q hqa ha,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_value b hn hb] at hv
    exact False.elim (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k
      ⟨u.val b.val.1, hb⟩ (v.val q) hv.symm)
  · obtain ⟨q, hqb⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.exists_some_of_pivot b hb
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_value a hn ha,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_value b hn q hqb hb] at hv
    exact False.elim (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m n k
      ⟨u.val a.val.1, ha⟩ (v.val q) hv)
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_value a hn ha,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_value b hn hb] at hv
    have hu := congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m n k hv)
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique a.property.1 b.val.1 hu.symm).symm

/-- 概要：二段切断から実際の非零合成切断への写像は単射（BF §2.2.6）。
方針：外側位置を切断点ラベルで決め、内側位置を接頭語長または二部分割で復元する。
規約：頂点入力は none、辺入力は some の有限添字を保持する。
使われ方：部分合成則で有限和を対応させる全単射の単射側。 -/
lemma toCompositeCut_injective (hn : 0 < n) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.toCompositeCut (u := u) (v := v) (k := k) hn) := by
  intro a b h
  have houter := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.toCompositeCut_outer_injective hn a b h
  have hr := congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn => x.val.1) h
  have hq := congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositeEdgeCut u v k hn => x.val.2) h
  change a.partition = b.partition at hr
  change a.compositePosition = b.compositePosition at hq
  apply Subtype.ext
  refine Prod.ext houter ?_
  cases ha : a.val.2 with
  | none =>
    cases hb : b.val.2 with
    | none => rfl
    | some q =>
      have HA := a.property.2
      have HB := b.property.2
      rw [ha] at HA
      rw [hb, ← houter] at HB
      exact False.elim (HA.1 HB.1)
  | some q =>
    cases hb : b.val.2 with
    | none =>
      have HA := a.property.2
      have HB := b.property.2
      rw [ha, houter] at HA
      rw [hb] at HB
      exact False.elim (HB.1 HA.1)
    | some s =>
      congr 1
      by_cases hp : u.val a.val.1 = k
      · have hp' : u.val b.val.1 = k := by rwa [← houter]
        have H := congrArg Fin.val hq
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_val a q ha hp,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.compositePosition_pivot_val b s hb hp', hr, houter] at H
        exact Fin.ext (Nat.add_left_cancel H)
      · have hp' : u.val b.val.1 ≠ k := by rwa [← houter]
        have hc := a.occurrenceCount_eq_two_of_some_nonpivot q ha (Ne.symm hp)
        have H := congrArg (fun r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e) =>
          cast (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e)) hc) r) hr
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition_of_some_nonpivot a q ha (Ne.symm hp),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.partition_of_some_nonpivot b s hb hp'.symm] at H
        have hl : 0 < n + e := by omega
        have HC := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut hl) H
        simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut_two] using HC

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
