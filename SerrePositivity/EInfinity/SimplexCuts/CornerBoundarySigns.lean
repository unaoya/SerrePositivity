module

public import SerrePositivity.EInfinity.SimplexCuts.CornerDeletionSigns

/-!
# 混合角の実際の出力境界符号

Berger–Fresse §2.2.7、M14 L09a。
活動頂点の濃度で正次数を確認し、削除した同じ色列の符号を共通因子にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C145：活動頂点の色の出力次数は正。 -/
lemma outputDegree_pos_of_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ activeVertexPositions s v.val) :
    0 < outputDegree s v (label s v.val k) := by
  rw [← active_color_card]
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩

/-- C146：前に同色の頂点がある場合も出力次数は正。 -/
lemma outputDegree_pos_of_previous {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
    0 < outputDegree s v (label s v.val k) := by
  have h := outputDegree_pos_of_active s v (previousVertex (label s v.val) k hp)
    (previousVertex_active s v.val k hp)
  rwa [previousVertex_value (label s v.val) k hp] at h

/-- C147：水平・垂直の混合角を交換した実際の出力境界符号は反対。 -/
lemma outputBoundarySignAt_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -outputBoundarySignAt s v b.castSucc := by
  let t := s.swapSteps a b
  have hna : a ∉ t.val := by
    simpa only [t, BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  have hbc : b.castSucc = a.succ := Fin.ext hab
  have hs : label t v.val a.castSucc = label t v.val b.castSucc := by
    rw [hbc]
    exact congrArg v.val (t.step_of_notMem a hna).1.symm
  have hp : (Surjection.previousOccurrences (label t v.val) b.castSucc).Nonempty := by
    refine ⟨a.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hs⟩⟩
    change a.val < b.val
    omega
  have ho := outputDegree_pos_of_active s v b.castSucc (before_vertical_active s v.val b hb)
  have hn := outputDegree_pos_of_previous t v b.castSucc hp
  rw [outputBoundarySignAt_erase _ _ _ hn, outputBoundarySignAt_erase _ _ _ ho]
  change (-1 : ℤ) ^ positionExponent (s.swapSteps a b) v.val *
      erasedColorSign (label (s.swapSteps a b) v.val) b.castSucc * _ = _
  rw [erasedColorSign_swapSteps s v.val a b hab]
  have rearrange (P E D : ℤ) : P * E * D = E * (P * D) := by
    rw [mul_comm P E, mul_assoc]
  rw [rearrange, rearrange, signedDeletionCoefficient_swapSteps_hv s v.val a b hab ha hb,
    mul_neg]

/-- C148：逆向きの混合角でも同じ実際の境界符号の反転を得る。 -/
lemma outputBoundarySignAt_swapSteps_vh {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∈ s.val) :
    outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -outputBoundarySignAt s v b.castSucc := by
  have hna : a ∈ (s.swapSteps a b).val := by
    simpa only [BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  have hnb : b ∉ (s.swapSteps a b).val := by
    simpa only [BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_right] using ha
  have h := outputBoundarySignAt_swapSteps_hv (s.swapSteps a b) v a b hab hna hnb
  rw [BarrattEccles.ShufflePath.swapSteps_swapSteps] at h
  simpa only [neg_neg] using (congrArg (fun z : ℤ => -z) h).symm

end SerrePositivity.EInfinity.SimplexCuts
