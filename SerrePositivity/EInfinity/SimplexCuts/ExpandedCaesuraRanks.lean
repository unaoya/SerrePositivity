module

public import SerrePositivity.EInfinity.SimplexCuts.ErasedCaesuraRanks
public import SerrePositivity.EInfinity.SimplexCuts.CornerEndpointCoordinates

/-!
# 展開色列のcaesura順位と経路の座標

Berger–Fresse §2.2.7、M14 L09a。
接頭部の活動頂点を垂直辺と元の語のcaesuraに分け、両種類の境界符号へ使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C170：展開色列のcaesura順位は、垂直座標と元の語の水平接頭順位の和。 -/
lemma caesuraRank_label {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
    Surjection.caesuraRank (label s v) k =
      (s.vertical k).val + Surjection.caesuraRank v (s.horizontal k) := by
  refine Fin.induction ?_ (fun i ih => ?_) k
  · have hh : s.horizontal 0 = 0 := by
      apply Fin.ext
      change (s.val.filter (fun i => i.val < 0)).card = 0
      simp
    have hv : s.vertical 0 = 0 := by
      apply Fin.ext
      change (s.valᶜ.filter (fun i => i.val < 0)).card = 0
      simp
    rw [hh, hv]
    simp [Surjection.caesuraRank]
  · rw [caesuraRank_adjacent (label s v) i.castSucc i.succ rfl, ih]
    by_cases hi : i ∈ s.val
    · have hs := s.step_of_mem i hi
      have hc := before_horizontal_active_iff s v i hi
      simp only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rw [caesuraRank_adjacent v (s.horizontal i.castSucc) (s.horizontal i.succ) hs.1,
        hs.2]
      simp only [hc]
      omega
    · have hs := s.step_of_notMem i hi
      have hc := (Finset.mem_filter.mp (before_vertical_active s v i hi)).2
      rw [ite_eq_left hc, hs.1]
      omega

end SerrePositivity.EInfinity.SimplexCuts
