module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapCoverage
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionMembers

/-!
模型。文献の定義との比較は後で
# 全射語の合成語の全射性

概要：Berger–Fresse §1.2.4 の各合成語は全ての出力ラベルを持つことを示す。
方針：BE の入力ラベル分解で残りの外側と内側に分け、各所属補題を適用する。
規約：nullary の空語の挿入も含む。
使われ方：合成語の正規化では非全射性による零項が現れないことを保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：各合成語は全ての出力ラベルを含む（BF §1.2.4）。
方針：既存の挿入ラベルの直和分解を使い、元の二つの全射性を所属へ移す。
規約：内側 arity が零なら内側ラベルの分岐は存在しない。
使われ方：合成語を全射として扱い、非退化性だけを別に検査する。 -/
lemma compositeWord_mem {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (a : Fin (m + n)) : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r := by
  have hsplit := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm_apply_apply a
  cases hcase : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a with
  | inl b =>
    have he : a = _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b := by
      simpa only [hcase, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition] using hsplit.symm
    rw [he]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remaining_mem_substitute k (List.ofFn u.val) (r.segments v.val) b.val b.property
    obtain ⟨i, hi⟩ := u.surjective b.val
    exact List.mem_ofFn.mpr ⟨i, hi⟩
  | inr b =>
    have he : a = _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b := by
      simpa only [hcase, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition] using hsplit.symm
    rw [he]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_mem_substitute k (List.ofFn u.val) (r.segments v.val)
      (by rw [r.segments_length]; rfl) b
    obtain ⟨i, hi⟩ := v.surjective b
    exact hi ▸ r.value_mem_segments v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) i

/-- 概要：合成語を有限位置で読む関数は全射（BF §1.2.4）。
方針：各値のリスト所属を実際の有限添字へ移す。
規約：合成語の隣接非一致は別に証明する。
使われ方：合成語の基底条件のうち全射性を供給する。 -/
lemma compositeWord_surjective {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    Function.Surjective (fun j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r).length =>
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[j.val]) := by
  intro a
  obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_mem u v k r a)
  exact ⟨⟨j, hj⟩, hv⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
