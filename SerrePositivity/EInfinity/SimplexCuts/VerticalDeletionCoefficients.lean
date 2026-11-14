module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalActiveMaxima
public import SerrePositivity.EInfinity.SimplexCuts.MixedCornerTerms
public import SerrePositivity.EInfinity.SimplexCuts.ExpandedCaesuraRanks

/-!
# 垂直境界の展開語の削除係数

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
直前の同色位置と垂直辺を使い、展開語の削除係数を入力頂点と元の語の接頭順位で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C230：隣接同色の後の位置の削除係数は、その位置のcaesura順位の符号。 -/
lemma deletionCoefficient_eq_rank_of_adjacent {N r : ℕ} (v : Fin N → Fin r)
    (a b : Fin N) (hab : b.val = a.val + 1) (hcolor : v a = v b) :
    Surjection.deletionCoefficient v b = (-1 : ℤ) ^ Surjection.caesuraRank v b := by
  by_cases hb : Surjection.Caesura v b
  · exact Surjection.deletionCoefficient_of_caesura v b hb
  · have hlt : a < b := by change a.val < b.val; omega
    have ha : Surjection.Caesura v a := ⟨b, hlt, hcolor.symm⟩
    have hmem : a ∈ Surjection.previousOccurrences v b :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hcolor⟩
    have hp : (Surjection.previousOccurrences v b).Nonempty := ⟨a, hmem⟩
    have hprev : previousVertex v b hp = a := by
      apply le_antisymm
      · have hval : (previousVertex v b hp).val < b.val := previousVertex_lt v b hp
        change (previousVertex v b hp).val ≤ a.val
        omega
      · exact (Surjection.previousOccurrences v b).le_max' a hmem
    have hf := Surjection.deletionCoefficient_final v b hb hp
    change Surjection.deletionCoefficient v b = -Surjection.deletionCoefficient v
      (previousVertex v b hp) at hf
    rw [hprev, Surjection.deletionCoefficient_of_caesura v a ha] at hf
    have hr := caesuraRank_adjacent v a b hab
    rw [ite_eq_left ha] at hr
    rw [hf, hr, pow_succ]
    simp only [mul_neg, mul_one]

/-- C231：垂直頂点は活動的か、同色を持つ直前の垂直辺の終点。 -/
lemma vertical_vertex_active_or_incoming {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.Caesura (label s v) k ∨
      ∃ e : Fin (m + (q + 1)), e.succ = k ∧ e ∉ s.val := by
  by_cases hlast : k.val = m + (q + 1)
  · right
    let e : Fin (m + (q + 1)) := ⟨m + (q + 1) - 1, by omega⟩
    have he : e.succ = k := by
      apply Fin.ext
      change m + (q + 1) - 1 + 1 = k.val
      omega
    exact ⟨e, he, vertical_kind_incoming_not_mem s k hk e he⟩
  · let e : Fin (m + (q + 1)) := ⟨k.val, by have := k.isLt; omega⟩
    have he : e.castSucc = k := Fin.ext rfl
    have hnot := vertical_kind_outgoing_not_mem s k hk e he
    have hs := (s.step_of_notMem e hnot).1
    rw [he] at hs
    refine Or.inl ⟨e.succ, ?_, congrArg v hs⟩
    change k.val < k.val + 1
    omega

/-- C232：垂直頂点の削除係数は、入力頂点と元の語の接頭順位の和の符号。 -/
lemma deletionCoefficient_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    Surjection.deletionCoefficient (label s v) k =
      (-1 : ℤ) ^ ((s.vertical k).val + Surjection.caesuraRank v (s.horizontal k)) := by
  rcases vertical_vertex_active_or_incoming s v k hk with hc | ⟨e, he, hnot⟩
  · rw [Surjection.deletionCoefficient_of_caesura _ _ hc, caesuraRank_label]
  · have hs := (s.step_of_notMem e hnot).1
    rw [he] at hs
    have hcolor : label s v e.castSucc = label s v k := congrArg v hs.symm
    have hbase := deletionCoefficient_eq_rank_of_adjacent (label s v) e.castSucc k
      (congrArg (fun j : Fin (m + (q + 1) + 1) => j.val) he.symm) hcolor
    rw [caesuraRank_label] at hbase
    exact hbase

/-- C233：垂直頂点の指定色の出力次数は正。 -/
lemma outputDegree_pos_vertical {m q r : ℕ} (s : Cut m (q + 1))
    (v : Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : boundaryVertexKind s k = .vertical) :
    0 < outputDegree s v (label s v.val k) := by
  rcases vertical_vertex_active_or_incoming s v.val k hk with hc | ⟨e, he, hnot⟩
  · exact outputDegree_pos_of_active s v k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · have h := outputDegree_pos_after_vertical s v e hnot
    simpa only [he] using h

end SerrePositivity.EInfinity.SimplexCuts
