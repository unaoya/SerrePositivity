module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorPathMap
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositionInjective

/-!
# 元の部分語分解で読む挿入色の写像の値

Berger–Fresse §2.2.6、M14 L12a のC451の逆の照合。
元の位置の分解の一意性を使い、指定された同じ内側頂点で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 挿入色の写像は、元の任意の同じ部分語分解で計算できる（BF §2.2.6）。 -/
lemma insertedColorPathMap_val_of_segment {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (hx : c.2.horizontal x.val = positiveCompositeSegmentPosition u v k c.1 i z) :
    (insertedColorPathMap u v k c b x).val =
      positiveCompositeSegmentInnerVertex u v k c i z x.val hx := by
  unfold insertedColorPathMap
  exact positiveCompositeSegmentInnerVertex_eq_of_same_source u v k c _ _ x.val _ i z hx

end SerrePositivity.EInfinity.SimplexCuts
