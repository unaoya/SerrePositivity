module

public import SerrePositivity.EInfinity.SimplexCuts.InactiveColorDegrees
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
# 混合角の座標と水平辺の直前の区間端点

Berger–Fresse §2.2.7、M14 L09a。
既存の辺の増分と角交換の座標保存から、変わる一頂点を同定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C128：水平辺の直前は、その水平座標の区間の最後の頂点。 -/
lemma interval_max_before_horizontal {m q : ℕ} (s : Cut m q) (a : Fin (m + q))
    (ha : a ∈ s.val) :
    (intervalPositions s (s.horizontal a.castSucc)).max'
      (intervalPositions_nonempty s (s.horizontal a.castSucc)) = a.castSucc := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro j hj
    by_contra h
    have hlt : a.castSucc < j := lt_of_not_ge h
    have haj : a.succ ≤ j := by change a.val + 1 ≤ j.val; exact hlt
    have hmono := s.horizontal.monotone haj
    have hc := (Finset.mem_filter.mp hj).2
    have hs := (s.step_of_mem a ha).1
    have hv := congrArg Fin.val hc
    change (s.horizontal a.succ).val ≤ (s.horizontal j).val at hmono
    omega

/-- C129：水平辺の直前の活動性は、元の語のその区間のcaesuraだけで決まる。 -/
lemma before_horizontal_active_iff {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∈ s.val) :
    a.castSucc ∈ activeVertexPositions s v ↔ Surjection.Caesura v (s.horizontal a.castSucc) := by
  simp only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [caesura_label_iff s v (s.horizontal a.castSucc) a.castSucc rfl,
    interval_max_before_horizontal s a ha, lt_self_iff_false, false_or]

/-- C130：垂直辺の始点には同色の終点があるため活動的。 -/
lemma before_vertical_active {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val) : a.castSucc ∈ activeVertexPositions s v :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.succ, a.castSucc_lt_succ,
    congrArg v (s.step_of_notMem a ha).1⟩

/-- C131：垂直辺の終点の直前同色頂点は、その辺の始点そのもの。 -/
lemma previousVertex_after_vertical {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a : Fin (m + q)) (ha : a ∉ s.val)
    (hp : (Surjection.previousOccurrences (label s v) a.succ).Nonempty) :
    previousVertex (label s v) a.succ hp = a.castSucc := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.castSucc_lt_succ,
      congrArg v (s.step_of_notMem a ha).1.symm⟩
  · intro j hj
    have hlt := (Finset.mem_filter.mp hj).2.1
    change j.val ≤ a.val
    change j.val < a.val + 1 at hlt
    omega

/-- C132：水平・垂直の混合角を交換すると、中間の区間番号は一つ前、垂直座標は一つ後。 -/
lemma swapSteps_hv_coordinates {m q : ℕ} (s : Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    (s.swapSteps a b).horizontal b.castSucc = s.horizontal a.castSucc ∧
      ((s.swapSteps a b).vertical b.castSucc).val = (s.vertical b.castSucc).val + 1 := by
  have hbc : b.castSucc = a.succ := Fin.ext hab
  have hne : (a.castSucc : Fin (m + q + 1)).val ≠ b.val := by
    change a.val ≠ b.val
    omega
  have hna : a ∉ (s.swapSteps a b).val := by
    simpa only [BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  constructor
  · rw [hbc, (s.swapSteps a b).step_of_notMem a hna |>.1,
      s.horizontal_swapSteps a b hab a.castSucc hne]
  · rw [hbc, (s.swapSteps a b).step_of_notMem a hna |>.2,
      s.vertical_swapSteps a b hab a.castSucc hne, (s.step_of_mem a ha).2]

end SerrePositivity.EInfinity.SimplexCuts
