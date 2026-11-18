module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OccurrenceCardinalities
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeFirstPositionOrder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeRemainingPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCuts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SubstitutionCounts
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Fintype.EquivFin

/-!
模型。文献の定義との比較は後で
# 元の残り色の全出現位置の順序同値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の指定面の照合。
元の文字の出現回数と同じ接頭位置を保ち、有限濃度によって全出現を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の残り色の出現回数は、同じ合成語でも変わらない（BF §2.2.6）。 -/
lemma positiveCompositeWord_remaining_count {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val a.val := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord_list]
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn u.val) (r.segments v.val)).count
    (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remaining_count_substitute]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_occurrenceCount u a.val).symm

/-- 元の残り色の全出現位置を、同じ合成ブロックの最初の位置へ送る順序同値（BF §2.2.6）。 -/
def remainingWordPositionOrderIso {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val a.val) ≃o
      ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)) := by
  let f : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val a.val) →
      ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)) := fun p =>
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p.val = a.val := (Finset.mem_filter.mp p.property).2
      have hpk : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p.val ≠ k := fun h => a.property (hp.symm.trans h)
      exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeFirstPosition_label u v k r p.val hpk).trans
        (congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k) (Subtype.ext hp))⟩⟩
  have hf : StrictMono f := by
    intro p p' h
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition_strictMono u v k r h
  have hc : Fintype.card ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val a.val) =
      Fintype.card ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)) := by
    simp only [Fintype.card_coe, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.occurrences_card_eq_count]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeWord_remaining_count u v k r a).symm
  have hb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf.injective, hc⟩
  exact StrictMono.orderIsoOfSurjective f hf hb.2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
