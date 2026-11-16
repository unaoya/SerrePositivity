module

public import SerrePositivity.EInfinity.SimplexCuts.ColorOrderActiveTransport
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositionInjective

/-!
# 異なる挿入色の元の頂点順序の反映

Berger–Fresse §2.2.6、M14 L12a の C452。
色別の指定同値を変更せず、異なる色の対についても元の経路番号を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内側頂点の写像は、色によらず元の順序を反映する（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_lt_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx <
      positiveCompositeSegmentInnerVertex u v k c j w y hy ↔ x < y := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hyx | heq
    · have hrev := positiveCompositeSegmentInnerVertex_strict_order
        u v k c j w y hy i z x hx hyx
      exact (not_lt_of_ge h.le) hrev
    · subst y
      have he := positiveCompositeSegmentInnerVertex_eq_of_same_source
        u v k c i z x hx j w hy
      exact (ne_of_lt h) he
  · exact positiveCompositeSegmentInnerVertex_strict_order u v k c i z x hx j w y hy

/-- 挿入色が異なっても、指定した同じ色別同値は順序を反映（BF §2.2.6）。 -/
lemma insertedColorPathOrderIso_cross_lt_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b b' : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)))
    (y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b'))) :
    (insertedColorPathOrderIso u v k c b x).val <
      (insertedColorPathOrderIso u v k c b' y).val ↔ x.val < y.val := by
  change (insertedColorPathMap u v k c b x).val <
    (insertedColorPathMap u v k c b' y).val ↔ x.val < y.val
  unfold insertedColorPathMap
  exact positiveCompositeSegmentInnerVertex_lt_iff u v k c _ _ _ _ _ _ _ _

end SerrePositivity.EInfinity.SimplexCuts
