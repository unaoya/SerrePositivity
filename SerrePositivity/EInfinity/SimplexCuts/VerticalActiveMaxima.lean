module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalVertexEdges
public import SerrePositivity.EInfinity.SimplexCuts.IntervalExtrema
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
# 垂直境界では活動区間の右端が残る

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
次の垂直辺を読む。終端では元の最後の区間にcaesuraがないことを使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C227：垂直の削除頂点は、活動区間の右端ではない。 -/
lemma hi_vertex_ne_vertical_of_caesura {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical)
    (i : Fin (m + 1)) (hi : Surjection.Caesura v i) :
    (intervalPositions s i).max' (intervalPositions_nonempty s i) ≠ k := by
  intro hmax
  have hhi : s.horizontal k = i := by
    rw [← hmax]
    exact horizontal_hi_vertex s i
  by_cases hlast : k.val = m + (q + 1)
  · have hklast : k = Fin.last (m + (q + 1)) := Fin.ext hlast
    rw [hklast, s.horizontal_endpoints.2] at hhi
    have he : i = Fin.last m := hhi.symm
    subst i
    obtain ⟨j, hij, _⟩ := hi
    have hj := j.isLt
    change m < j.val at hij
    omega
  · let e : Fin (m + (q + 1)) := ⟨k.val, by have := k.isLt; omega⟩
    have he : e.castSucc = k := Fin.ext rfl
    have hnot := vertical_kind_outgoing_not_mem s k hk e he
    have hs := (s.step_of_notMem e hnot).1
    rw [he, hhi] at hs
    have hb : e.succ ≤ (intervalPositions s i).max' (intervalPositions_nonempty s i) :=
      (intervalPositions s i).le_max' e.succ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    rw [hmax] at hb
    change k.val + 1 ≤ k.val at hb
    omega

end SerrePositivity.EInfinity.SimplexCuts
