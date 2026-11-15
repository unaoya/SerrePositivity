module

public import SerrePositivity.EInfinity.SimplexCuts.PositionExponentEdgeSum
public import SerrePositivity.EInfinity.SimplexCuts.OverlapInternalPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerRanks
public import SerrePositivity.EInfinity.SimplexCuts.WordCaesuraLengthTransport

/-!
# 元の内側切断の位置指数を部分語の内部で読む

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
報告 §289 の位置指数の再添字付け。同じ辺の所属だけを使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 内側位置指数は、同じ全部分語の内部の区切り高さの和（BF §2.2.6）。 -/
lemma positiveComposite_inner_positionExponent_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin ((c.1.val i).val - 1),
        if Surjection.Caesura v.val
            ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
        then hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i
          ⟨z.val, by have hz := z.isLt; omega⟩) else 0 := by
  rw [positionExponent_eq_edge_sum,
    sum_overlap_internal_positions c.1 (Surjection.occurrenceCount_pos u k)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  have hc := caesura_word_eq_mp (by omega : (n + 1) + e = n + e + 1) v
    (⟨c.1.start i + z.val, by
      have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩ : Fin (n + e + 1))
    (⟨c.1.start i + z.val, by
      have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩ : Fin ((n + 1) + e)) rfl
  change Surjection.Caesura (positiveWord v).val _ ↔ Surjection.Caesura v.val _ at hc
  exact ite_congr (propext hc) (fun _ => rfl) (fun _ => rfl)

end SerrePositivity.EInfinity.SimplexCuts
