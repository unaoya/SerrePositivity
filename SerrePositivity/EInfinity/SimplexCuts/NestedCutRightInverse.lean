module

public import SerrePositivity.EInfinity.SimplexCuts.NestedCompositeOuterCut
public import SerrePositivity.EInfinity.SimplexCuts.NestedInnerRankRecovery
public import SerrePositivity.EInfinity.SimplexCuts.CompositeNestedMap
public import SerrePositivity.EInfinity.SimplexCuts.CutHeightTransport

/-!
# 元の二段切断を復元する右逆の等式

Berger–Fresse §2.2.6、M14 L12a の逆の等式の証明分割。
外側Cutとその出力次数を厳密に合わせ、同じ内側順位へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C440：元の内側切断の高さを、同じ順位の差として読む（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_height_val {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    (cutHeights (positiveCompositeInnerCut u v k c) a).val =
      (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k
            (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))
          (positiveOccurrencePosition_value u k _)).val +
        ((cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val -
          lo (positiveCompositeOuterCut u v k c)
            (positiveOccurrencePosition u k
              (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))) := by
  rw [positiveCompositeInnerCut_heights]
  rfl

/-- C441：逆復元から射影すると、元の二段切断そのものに戻る（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_rightInverse {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) :
    Function.RightInverse (positiveNestedCompositeMap u v k (q := q))
      (positiveCompositeNestedMap u v k) := by
  intro c
  have ho := positiveNestedCompositeMap_outerCut u v k c
  apply Sigma.ext ho
  apply cutHeights_heq _ _ (congrArg (fun s => outputDegree s (positiveWord u) k) ho)
  intro a
  change (cutHeights (positiveCompositeInnerCut u v k (positiveNestedCompositeMap u v k c)) a).val =
    (cutHeights c.2 a).val
  rw [positiveCompositeInnerCut_height_val, ho]
  have hh := congrArg Fin.val (positiveNestedCompositeMap_heights u v k c (Sum.inr a))
  change (cutHeights (positiveNestedCompositeMap u v k c).2
      (compositeInnerEdge u v k (positiveNestedCompositeMap u v k c).1 a)).val =
    (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val at hh
  rw [hh]
  exact congrArg Fin.val (positiveNestedInnerRank_recover u v k c a)

end SerrePositivity.EInfinity.SimplexCuts
