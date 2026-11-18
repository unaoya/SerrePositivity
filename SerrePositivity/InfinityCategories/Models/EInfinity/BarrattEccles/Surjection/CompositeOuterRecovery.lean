module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecoveryLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceSuffixes

/-!
模型。文献の定義との比較は後で
# 合成語から元の外側語を一般に復元する

概要：Berger–Fresse §1.5.9 の外側語の復元と一意性を実際の compositeWord に対して証明する。
方針：挿入部分語の外側射影は指定値の反復であり、非空なら一文字へ縮約できる。
規約：内側語長は正。元の外側語の非退化性で縮約後に元の語そのものを得る。
使われ方：逆構成で得る外側語と元の外側語の一意性を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：非空部分語を代入した語の外側射影を縮めると元の語の縮約（BF §1.5.9）。
方針：外側語で帰納し、各挿入部分語の指定値反復を一文字に戻す。
規約：元の語の非退化性はまだ要求しない。
使われ方：非退化な外側語を合成語から復元する。 -/
lemma collapse_outer_substitute {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hc : parts.length = xs.count k) (hp : ∀ part ∈ parts, part ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs := by
  induction xs generalizing parts with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp only [List.length_nil, List.count_cons_self] at hc; omega
      | cons part parts =>
        have ht : parts.length = xs.count k := by simpa only [List.length_cons,
          List.count_cons_self, Nat.add_right_cancel_iff] using hc
        have hparts : ∀ q ∈ parts, q ≠ [] := fun q hq => hp q (List.mem_cons_of_mem part hq)
        have hpos : 0 < part.length := List.length_pos_iff.mpr (hp part (by simp))
        have he : part.length = (part.length - 1) + 1 := by omega
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons, List.map_append,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_map_inserted, he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_replicate_append]
        exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend k) (ih parts ht hparts)
    · have ht : parts.length = xs.count k := by simpa [ha] using hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining]
      exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a) (ih parts ht hp)

/-- 概要：合成語から外側ラベルを戻して連続重複を縮約した語（BF §1.5.9）。
方針：挿入ラベルは指定値へ戻し、連続反復だけを一文字にする。
規約：離れた指定値は保持する。
使われ方：元の外側語の一般の逆写像。 -/
def outerWord {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + n))) :
    List (Fin (m + 1)) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k))

/-- 概要：正の内側語長の合成語から元の外側語を復元できる（BF §1.5.9）。
方針：各分割成分の非空性と元の外側語の非退化性を縮約へ渡す。
規約：元の内側語や分割を逆写像の入力にしない。
使われ方：外側語の一意性と逆構成の往復。 -/
lemma outerWord_compositeWord {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hl : 0 < n + e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r) = List.ofFn u.val := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_outer_substitute k (List.ofFn u.val) (r.segments v.val)
    (by rw [r.segments_length]; rfl)]
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate u.val u.nondegenerate)
  · intro part hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    intro he
    have hlen := r.segment_length v.val i
    have hpos := r.positive hl i
    rw [he, List.length_nil] at hlen
    omega

/-- 概要：等しい合成語を与える元の外側語のリストは等しい（BF §1.5.9）。
方針：合成語だけからの同じ外側復元を両辺へ適用する。
規約：内外の元の次数は左右で異なってもよい。
使われ方：全合成項の対応で元の外側語を一意に決める。 -/
lemma outer_list_unique {m n d e d' e' : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (u' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d') (v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e') (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u'.val k) (n + e'))
    (hl : 0 < n + e) (hl' : 0 < n + e')
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u' v' k r') :
    List.ofFn u.val = List.ofFn u'.val := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k) he
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_compositeWord u v k r hl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_compositeWord u' v' k r' hl'] using h

/-- 概要：同じ次数の外側基底語は合成語から一意に決まる（BF §1.5.9）。
方針：復元したリストの一致を有限列と部分型の一致へ戻す。
規約：元の内側語と分割は左右で異なってよい。
使われ方：全合成項の対応の単射性の外側成分。 -/
lemma outer_unique {m n d e e' : ℕ}
    (u u' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e')
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u'.val k) (n + e'))
    (hl : 0 < n + e) (hl' : 0 < n + e')
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u' v' k r') : u = u' := by
  apply Subtype.ext
  exact List.ofFn_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outer_list_unique u v u' v' k r r' hl hl' he)

/-- 概要：等しい合成語を与える元の内外の次数はともに等しい（BF §1.5.9）。
方針：復元した外側語の長さと全合成語の長さを比較する。
規約：元の次数を等しいと仮定しない。
使われ方：逆構成で復元する次数の一意性。 -/
lemma input_degrees_unique {m n d e d' e' : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (u' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d') (v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e') (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u'.val k) (n + e'))
    (hl : 0 < n + e) (hl' : 0 < n + e')
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u' v' k r') : d = d' ∧ e = e' := by
  have ho := congrArg List.length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outer_list_unique u v u' v' k r r' hl hl' he)
  have hc := congrArg List.length he
  simp only [List.length_ofFn] at ho
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length] at hc
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
