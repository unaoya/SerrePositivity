module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SubstitutionNodup
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ListCutValidity

/-!
模型。文献の定義との比較は後で
# 指定色以外の切断点での代入と非退化性

概要：Berger–Fresse §2.2.6 の非切断点色への代入で、外側切断点を実際の合成語へ保つ。
方針：合成語の左右の take・drop を、元の左右への代入として評価する。
規約：各挿入部分語の重複消滅だけを要求し、部分語同士の非交差は要求しない。
使われ方：二段切断の頂点入力・二出現辺入力の非退化性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定色以外の位置までの代入は直前の代入にその残りラベルを加える（BF §2.2.6）。
方針：接頭語の次の一文字を取り出し、代入の連結則を評価する。
規約：部分語列は任意。
使われ方：非切断点色の左側切断の同定。 -/
lemma substitute_take_at_non_slot {m n l : ℕ} (u : Fin l → Fin (m + 1))
    (k : Fin (m + 1)) (p : Fin l) (hp : u p ≠ k) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u).take (p.val + 1)) parts =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u).take p.val) parts ++
        [_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u p, hp⟩] := by
  have hl : p.val < (List.ofFn u).length := by simpa only [List.length_ofFn] using p.isLt
  rw [List.take_succ_eq_append_getElem hl, List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_append,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute]

/-- 概要：指定色以外の位置からの代入はその残りラベルで始まる（BF §2.2.6）。
方針：drop の先頭を元の同じ位置の文字として評価する。
規約：指定色以外なので内側部分語を消費しない。
使われ方：非切断点色の右側切断の同定。 -/
lemma substitute_drop_at_non_slot {m n l : ℕ} (u : Fin l → Fin (m + 1))
    (k : Fin (m + 1)) (p : Fin l) (hp : u p ≠ k) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u).drop p.val) parts =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u p, hp⟩ ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u).drop (p.val + 1)) parts := by
  have hl : p.val < (List.ofFn u).length := by simpa only [List.length_ofFn] using p.isLt
  rw [List.drop_eq_getElem_cons hl, List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hp]

/-- 概要：実際の合成切断の左リストは元の左リストへの同じ分割の代入（BF §2.2.6）。
方針：合成語を外側切断点で分解し、接頭語長とその直後の一文字を使う。
規約：切断点の文字を含む。
使われ方：左の非退化性を代入の Nodup で供給する。 -/
lemma compositeOuterPosition_prefix {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).val + 1) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (p.val + 1)) (r.segments v.val) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_take_at_non_slot u.val k p hp,
    List.take_length_add_append, List.take_succ_cons, List.take_zero]

/-- 概要：実際の合成切断の右リストは未消費分割の元の右リストへの代入（BF §2.2.6）。
方針：合成語の接頭語全長を除き、指定色以外の元位置からの代入を使う。
規約：元位置以前の出現回数だけ内側部分語列を消費する。
使われ方：右の非退化性を代入の Nodup で供給する。 -/
lemma compositeOuterPosition_suffix {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val).drop
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp).val =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop p.val)
        ((r.segments v.val).drop (((List.ofFn u.val).take p.val).count k)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_non_slot u v k r p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_drop_at_non_slot u.val k p hp,
    List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append]

/-- 概要：指定色以外の非零切断へ重複のない部分語を代入すると合成切断は非零（BF §2.2.6）。
方針：元の左右は Nodup なので各側に指定色は高々一回で、各部分語の Nodup で十分となる。
規約：実際の合成基底語を使い、内側 arity は正。
使われ方：二段切断の非切断点色分岐の共通の非退化性補題。 -/
lemma composite_non_slot_cut_nondegenerate {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p)
    (hr : ∀ part ∈ r.segments v.val, part.Nodup) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p hp) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_prefix]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_nodup_of_parts k _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup u.val p h) hr
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_suffix]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_nodup_of_parts k _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup u.val p h)
    intro part hpart
    exact hr part (List.mem_of_mem_drop hpart)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
