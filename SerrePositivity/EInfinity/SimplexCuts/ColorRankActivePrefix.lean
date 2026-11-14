module

public import SerrePositivity.EInfinity.SimplexCuts.ActiveBoundarySigns
public import SerrePositivity.EInfinity.SimplexCuts.ExpandedCaesuraRanks
public import SerrePositivity.EInfinity.SimplexCuts.ColorIntervalRanks

/-!
# 元の色別順位と先行する他色の活動頂点数

Berger–Fresse §2.2.4–6、M14 L12a のC452。
既存のcaesuraRank_labelと面番号の濃度を、同じ水平座標と色別順位で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の色別順位と先行他色数の和は、同じ高さと元の区切り順位の和（BF §2.2.4）。 -/
lemma colorRank_add_other_active_prefix {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1))
    (j : Fin (outputDegree s v a + 1)) (hm : j ∈ colorIntervalRanks s v a p) :
    j.val + ((activeVertexPositions s v.val).filter (fun z =>
      z < colorPositionEquiv s v ⟨a, j⟩ ∧ label s v.val z ≠ a)).card =
      (vertices s v a j).val + Surjection.caesuraRank v.val p := by
  let x := colorPositionEquiv s v ⟨a, j⟩
  let S := (activeVertexPositions s v.val).filter (fun z => z < x)
  have hx : s.horizontal x = p := (Finset.mem_filter.mp hm).2
  have hsameSet : S.filter (fun z => label s v.val z = a) =
      (activeVertexPositions s v.val).filter (fun z => z < x ∧ label s v.val z = a) := by
    ext z
    simp only [S, Finset.mem_filter, and_assoc]
  have hotherSet : S.filter (fun z => label s v.val z ≠ a) =
      (activeVertexPositions s v.val).filter (fun z => z < x ∧ label s v.val z ≠ a) := by
    ext z
    simp only [S, Finset.mem_filter, and_assoc]
  have hsame : (S.filter (fun z => label s v.val z = a)).card = j.val := by
    have hr := vertexRank_eq_active_card s v.val x
    rw [show label s v.val x = a from label_colorPositionEquiv s v a j,
      vertexRank_colorPositionEquiv] at hr
    rw [hsameSet]
    exact hr.symm
  have hrank : S.card = Surjection.caesuraRank (label s v.val) x := by
    apply congrArg Finset.card
    ext z
    simp only [S, activeVertexPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact and_comm
  have htotal : S.card = (vertices s v a j).val + Surjection.caesuraRank v.val p := by
    have h := caesuraRank_label s v.val x
    rw [hx] at h
    exact hrank.trans h
  have hsplit := S.card_filter_add_card_filter_not (fun z => label s v.val z = a)
  rw [hsame, hotherSet] at hsplit
  exact hsplit.trans htotal

/-- 同じ元の水平区間内では、先行する他色の活動頂点の集合は変わらない（BF §2.2.4）。 -/
lemma other_active_prefix_eq_on_interval {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin r) (p : Fin (m + 1)) (hp : v p = a)
    (x y : Fin (m + q + 1)) (hx : s.horizontal x = p) (hy : s.horizontal y = p) :
    (activeVertexPositions s v).filter (fun z => z < x ∧ label s v z ≠ a) =
      (activeVertexPositions s v).filter (fun z => z < y ∧ label s v z ≠ a) := by
  ext z
  by_cases hz : label s v z = a
  · simp only [Finset.mem_filter, hz, ne_eq, not_true_eq_false, and_false]
  · have he : z < x ↔ z < y := by
      constructor
      · intro hzx
        by_contra hn
        have hl := s.horizontal.monotone (le_of_not_gt hn)
        have hr := s.horizontal.monotone hzx.le
        rw [hy] at hl
        rw [hx] at hr
        have hzp : s.horizontal z = p := le_antisymm hr hl
        exact hz (by change v (s.horizontal z) = a; rw [hzp, hp])
      · intro hzy
        by_contra hn
        have hl := s.horizontal.monotone (le_of_not_gt hn)
        have hr := s.horizontal.monotone hzy.le
        rw [hx] at hl
        rw [hy] at hr
        have hzp : s.horizontal z = p := le_antisymm hr hl
        exact hz (by change v (s.horizontal z) = a; rw [hzp, hp])
    simp only [Finset.mem_filter, hz, ne_eq, not_false_eq_true, and_true]
    exact and_congr_right (fun _ => he)

end SerrePositivity.EInfinity.SimplexCuts
