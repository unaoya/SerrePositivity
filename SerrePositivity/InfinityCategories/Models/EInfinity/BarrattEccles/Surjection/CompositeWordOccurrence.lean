module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionConcatenation

/-!
模型。文献の定義との比較は後で
# 合成語の各出現での厳密な分解

概要：Berger–Fresse §1.5.7 の各挿入部分が、元の重なる分割の同じ番号の成分語であることを示す。
方針：任意の出現での代入分解を使い、消費済み部分語列の先頭を ofFn で評価する。
規約：内側の空語の一部分割も同じ式で扱う。
使われ方：全融合表の垂直成分と実際の compositeWord の挿入部分を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：合成語を第 i 出現の前半・実際の分割成分・後半へ分解（BF §1.5.7）。
方針：出現番号まで部分語を消費した列の先頭を指定成分へ戻す。
規約：成功表の選択や内側語の正長性を要求しない。
使われ方：融合出力の各垂直語を同じ出現の合成語へ接続する。 -/
lemma compositeWord_at_occurrence {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val) (r.segments v.val) ++
        (r.segment v.val i).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1))
            ((r.segments v.val).drop (i.val + 1)) := by
  have hp : ((r.segments v.val).drop i.val).headD [] = r.segment v.val i := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.headD_eq_head?_getD, List.head?_eq_getElem?,
      List.getElem?_drop, Nat.add_zero, List.getElem?_ofFn, dite_eq_left i.isLt,
      Option.getD_some]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_at_occurrence u.val k i (r.segments v.val)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord, hp] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
