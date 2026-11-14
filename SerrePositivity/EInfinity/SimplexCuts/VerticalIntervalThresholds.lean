module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalVertexEdges
public import SerrePositivity.EInfinity.SimplexCuts.IntervalExtrema
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
# 垂直の削除頂点と区間の右端の閾値

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
指定区間より前の右端は直前の垂直辺より前にあり、指定区間以後の右端は削除頂点以後にある。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C228：入力の削除頂点以後にある右端は、その区間以後のものに限る。 -/
lemma vertical_vertex_le_hi_iff {m q : ℕ} (s : Cut m (q + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (i : Fin (m + 1)) : (s.vertical k).val ≤ hi s i ↔ s.horizontal k ≤ i := by
  let j := (intervalPositions s i).max' (intervalPositions_nonempty s i)
  have hji : s.horizontal j = i := horizontal_hi_vertex s i
  constructor
  · intro hy
    by_contra hnot
    have hlt : i < s.horizontal k := lt_of_not_ge hnot
    have hjk : j < k := by
      by_contra h
      have hm := s.horizontal.monotone (le_of_not_gt h)
      rw [hji] at hm
      exact (not_le_of_gt hlt) hm
    have hjval : j.val < k.val := hjk
    have hk0 : 0 < k.val := by omega
    let e : Fin (m + (q + 1)) := ⟨k.val - 1, by have := k.isLt; omega⟩
    have he : e.succ = k := Fin.ext (by change k.val - 1 + 1 = k.val; omega)
    have hnotmem := vertical_kind_incoming_not_mem s k hk e he
    have hs := (s.step_of_notMem e hnotmem).2
    rw [he] at hs
    have hjle : j ≤ e.castSucc := by change j.val ≤ k.val - 1; omega
    have hm : (s.vertical j).val ≤ (s.vertical e.castSucc).val := s.vertical.monotone hjle
    change (s.vertical k).val ≤ (s.vertical j).val at hy
    omega
  · intro hi
    by_cases hjk : k ≤ j
    · exact s.vertical.monotone hjk
    · have hmono := s.horizontal.monotone (le_of_lt (lt_of_not_ge hjk))
      rw [hji] at hmono
      have he : i = s.horizontal k := le_antisymm hmono hi
      have hkmem : k ∈ intervalPositions s i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm⟩
      exact False.elim (hjk ((intervalPositions s i).le_max' k hkmem))

end SerrePositivity.EInfinity.SimplexCuts
