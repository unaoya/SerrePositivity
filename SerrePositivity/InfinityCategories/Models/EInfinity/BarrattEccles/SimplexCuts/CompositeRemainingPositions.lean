module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeOuterEndpoints
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrencePosition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionCutPositions

/-!
模型。文献の定義との比較は後で
# 同じ合成語に残る外側の位置と文字

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の指定面の照合。
元の指定色以外の文字は、同じ接頭長で一文字のまま読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C451e：元の指定色以外の一文字で接頭長は一だけ増える（BF §2.2.6）。 -/
lemma compositePrefixLength_at_non_slot {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r (p.val + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val + 1 := by
  let p' : Fin ((m + 1) + d) := ⟨p.val, by have h := p.isLt; omega⟩
  have hw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p = u.val p' := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl
  have hu : u.val p' ≠ k := fun h => hp (hw.trans h)
  let pList : Fin (List.ofFn u.val).length := ⟨p.val, by simp only [List.length_ofFn]; omega⟩
  have hpList : (List.ofFn u.val)[pList.val] ≠ k := by
    simpa only [pList, List.getElem_ofFn] using hu
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_non_slot k (List.ofFn u.val)
    (r.segments v.val) pList hpList

/-- 元の残り色のブロックの最初と最後は同じ一文字の位置（BF §2.2.6）。 -/
lemma compositeFirstPosition_eq_last_of_non_slot {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k r p := by
  apply Fin.ext
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r (p.val + 1) - 1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_at_non_slot u v k r p hp]
  omega

/-- C451f：同じ合成位置の文字は、元の残り色の番号変更だけ（BF §2.2.6）。 -/
lemma positiveCompositeFirstPosition_label {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r p) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p, hp⟩ := by
  let p' : Fin ((m + 1) + d) := ⟨p.val, by have h := p.isLt; omega⟩
  have hw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p = u.val p' := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl
  have hu : u.val p' ≠ k := fun h => hp (hw.trans h)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r (by omega)).val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r p' hu) := by
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega) _ _ _ rfl
    _ = _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k ⟨u.val p', hu⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition u v k r (by omega) p' hu
    _ = _ := congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k) (Subtype.ext hw.symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
