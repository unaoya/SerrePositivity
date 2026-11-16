module

public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceCaesuraTransport
public import SerrePositivity.EInfinity.SimplexCuts.ActiveVertexCounts
public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorFaces

/-!
# 同じ色別全頂点の順序同値による活動頂点の移送

Berger–Fresse §2.2.4–6、M14 L12a のC452。
既存の重み付き逆転指数で数える活動頂点を、同じ全色別順序で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ全色別順序を持つ頂点は、同時に活動的になる（BF §2.2.4）。 -/
lemma colorOrderIso_active_iff {m m' q q' r r' : ℕ} (s : Cut m q) (t : Cut m' q')
    (v : Fin (m + 1) → Fin r) (w : Fin (m' + 1) → Fin r') (a : Fin r) (b : Fin r')
    (e : ↥(colorPositions s v a) ≃o ↥(colorPositions t w b))
    (x : ↥(colorPositions s v a)) :
    (e x).val ∈ activeVertexPositions t w ↔ x.val ∈ activeVertexPositions s v := by
  simp only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact caesura_iff_of_occurrenceOrderIso (label s v) (label t w) a b e x

/-- 元の挿入色の同じ順序同値は、元の活動頂点を保つ（BF §2.2.4–6）。 -/
lemma insertedColorPathOrderIso_active_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    (insertedColorPathOrderIso u v k c b x).val ∈
        activeVertexPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val ↔
      x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val :=
  colorOrderIso_active_iff _ _ _ _ _ _ (insertedColorPathOrderIso u v k c b) x

end SerrePositivity.EInfinity.SimplexCuts
