module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerDeletionSigns

/-!
模型。文献の定義との比較は後で
# 混合角の実際の出力境界符号

Berger–Fresse §2.2.7、M14 L09a。
活動頂点の濃度で正次数を確認し、削除した同じ色列の符号を共通因子にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C145：活動頂点の色の出力次数は正。 -/
lemma outputDegree_pos_of_active {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val) :
    0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.active_color_card]
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩

/-- C146：前に同色の頂点がある場合も出力次数は正。 -/
lemma outputDegree_pos_of_previous {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty) :
    0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_active s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k hp)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_active s v.val k hp)
  rwa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_value (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k hp] at h

/-- C147：水平・垂直の混合角を交換した実際の出力境界符号は反対。 -/
lemma outputBoundarySignAt_swapSteps_hv {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v b.castSucc := by
  let t := s.swapSteps a b
  have hna : a ∉ t.val := by
    simpa only [t, _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  have hbc : b.castSucc = a.succ := Fin.ext hab
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label t v.val a.castSucc = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label t v.val b.castSucc := by
    rw [hbc]
    exact congrArg v.val (t.step_of_notMem a hna).1.symm
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label t v.val) b.castSucc).Nonempty := by
    refine ⟨a.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hs⟩⟩
    change a.val < b.val
    omega
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_active s v b.castSucc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.before_vertical_active s v.val b hb)
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_previous t v b.castSucc hp
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_erase _ _ _ hn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_erase _ _ _ ho]
  change (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent (s.swapSteps a b) v.val *
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v.val) b.castSucc * _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign_swapSteps s v.val a b hab]
  have rearrange (P E D : ℤ) : P * E * D = E * (P * D) := by
    rw [mul_comm P E, mul_assoc]
  rw [rearrange, rearrange, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.signedDeletionCoefficient_swapSteps_hv s v.val a b hab ha hb,
    mul_neg]

/-- C148：逆向きの混合角でも同じ実際の境界符号の反転を得る。 -/
lemma outputBoundarySignAt_swapSteps_vh {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∉ s.val) (hb : b ∈ s.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt (s.swapSteps a b) v b.castSucc =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v b.castSucc := by
  have hna : a ∈ (s.swapSteps a b).val := by
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  have hnb : b ∉ (s.swapSteps a b).val := by
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_right] using ha
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_swapSteps_hv (s.swapSteps a b) v a b hab hna hnb
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath.swapSteps_swapSteps] at h
  simpa only [neg_neg] using (congrArg (fun z : ℤ => -z) h).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
