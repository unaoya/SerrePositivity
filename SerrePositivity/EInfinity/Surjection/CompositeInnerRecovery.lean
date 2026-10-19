module

public import SerrePositivity.EInfinity.Surjection.CompositeInnerProjection
public import SerrePositivity.EInfinity.Surjection.CompositeOuterRecovery
public import SerrePositivity.EInfinity.Surjection.OverlapCollapse

/-!
# 合成語から元の内側語を復元し内外の語を一意に決める

概要：Berger–Fresse §1.5.9 の内側語の復元と元の両語の一意性を証明する。
方針：内側射影で得た全成分の共有端点を縮約し、元の内側語の非退化性を使う。
規約：正の内側語長。分割の一意性と元の表の復元は後続。
使われ方：合成項の全単射で元の語を出力だけから一意に復元する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.CompositeRecovery

/-- 概要：実際の合成語から元の内側語を復元できる（BF §1.5.9）。
方針：全分割成分の連結を共有端点で縮約して元の語へ戻す。
規約：元の内側語と分割を逆写像の入力にしない。
使われ方：内側語の一意性と逆構成の往復。 -/
lemma innerWord_compositeWord {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hl : 0 < n + e) :
    innerWord k (compositeWord u v k r) = List.ofFn v.val := by
  unfold innerWord
  rw [inner_compositeWord, r.collapse_segments hl (occurrenceCount_pos u k)]
  exact AdjacentCollapse.collapse_eq_self _
    (isChain_ofFn_of_nondegenerate v.val v.nondegenerate)

/-- 概要：等しい合成語を与える元の内側語のリストは等しい（BF §1.5.9）。
方針：合成語だけからの同じ内側復元を両辺へ適用する。
規約：元の内外の次数は左右で異なってもよい。
使われ方：全合成項の対応で元の内側語を一意に決める。 -/
lemma inner_list_unique {m n d e d' e' : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e)
    (u' : BasisWord (m + 1) d') (v' : BasisWord n e') (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e))
    (r' : OverlapPartition (occurrenceCount u'.val k) (n + e'))
    (hl : 0 < n + e) (hl' : 0 < n + e')
    (he : compositeWord u v k r = compositeWord u' v' k r') :
    List.ofFn v.val = List.ofFn v'.val := by
  have h := congrArg (innerWord k) he
  simpa only [innerWord_compositeWord u v k r hl, innerWord_compositeWord u' v' k r' hl'] using h

/-- 概要：同じ次数の内側基底語は合成語から一意に決まる（BF §1.5.9）。
方針：復元したリストの一致を有限列と部分型の一致へ戻す。
規約：元の外側語と分割は左右で異なってよい。
使われ方：全合成項の対応の単射性の内側成分。 -/
lemma inner_unique {m n d d' e : ℕ}
    (u : BasisWord (m + 1) d) (u' : BasisWord (m + 1) d') (v v' : BasisWord n e)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) (n + e))
    (r' : OverlapPartition (occurrenceCount u'.val k) (n + e))
    (hl : 0 < n + e) (he : compositeWord u v k r = compositeWord u' v' k r') : v = v' := by
  apply Subtype.ext
  exact List.ofFn_injective (inner_list_unique u v u' v' k r r' hl hl he)

/-- 概要：同じ合成語を与える元の内外の非退化基底語はそれぞれ等しい（BF §1.5.9）。
方針：出力だけからの外側・内側の二つの復元を合わせる。
規約：分割そのものの一意性はまだ要求しない。
使われ方：逆構成の元の二語の一意性。 -/
lemma input_words_unique {m n d e : ℕ}
    (u u' : BasisWord (m + 1) d) (v v' : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e))
    (r' : OverlapPartition (occurrenceCount u'.val k) (n + e))
    (hl : 0 < n + e) (he : compositeWord u v k r = compositeWord u' v' k r') :
    u = u' ∧ v = v' :=
  ⟨outer_unique u u' v v' k r r' hl hl he, inner_unique u u' v v' k r r' hl he⟩

end SerrePositivity.EInfinity.Surjection.CompositeRecovery
