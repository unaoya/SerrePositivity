module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalActiveMaxima
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedCornerTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ExpandedCaesuraRanks

/-!
模型。文献の定義との比較は後で
# 垂直境界の展開語の削除係数

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
直前の同色位置と垂直辺を使い、展開語の削除係数を入力頂点と元の語の接頭順位で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C230：隣接同色の後の位置の削除係数は、その位置のcaesura順位の符号。 -/
lemma deletionCoefficient_eq_rank_of_adjacent {N r : ℕ} (v : Fin N → Fin r)
    (a b : Fin N) (hab : b.val = a.val + 1) (hcolor : v a = v b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v b = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank v b := by
  by_cases hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v b
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura v b hb
  · have hlt : a < b := by change a.val < b.val; omega
    have ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a := ⟨b, hlt, hcolor.symm⟩
    have hmem : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v b :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hcolor⟩
    have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v b).Nonempty := ⟨a, hmem⟩
    have hprev : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v b hp = a := by
      apply le_antisymm
      · have hval : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v b hp).val < b.val := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_lt v b hp
        change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v b hp).val ≤ a.val
        omega
      · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v b).le_max' a hmem
    have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final v b hb hp
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v b = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v b hp) at hf
    rw [hprev, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura v a ha] at hf
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_adjacent v a b hab
    rw [ite_eq_left ha] at hr
    rw [hf, hr, pow_succ]
    simp only [mul_neg, mul_one]

/-- C231：垂直頂点は活動的か、同色を持つ直前の垂直辺の終点。 -/
lemma vertical_vertex_active_or_incoming {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k ∨
      ∃ e : Fin (m + (q + 1)), e.succ = k ∧ e ∉ s.val := by
  by_cases hlast : k.val = m + (q + 1)
  · right
    let e : Fin (m + (q + 1)) := ⟨m + (q + 1) - 1, by omega⟩
    have he : e.succ = k := by
      apply Fin.ext
      change m + (q + 1) - 1 + 1 = k.val
      omega
    exact ⟨e, he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_kind_incoming_not_mem s k hk e he⟩
  · let e : Fin (m + (q + 1)) := ⟨k.val, by have := k.isLt; omega⟩
    have he : e.castSucc = k := Fin.ext rfl
    have hnot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_kind_outgoing_not_mem s k hk e he
    have hs := (s.step_of_notMem e hnot).1
    rw [he] at hs
    refine Or.inl ⟨e.succ, ?_, congrArg v hs⟩
    change k.val < k.val + 1
    omega

/-- C232：垂直頂点の削除係数は、入力頂点と元の語の接頭順位の和の符号。 -/
lemma deletionCoefficient_vertical {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (v : Fin (m + 1) → Fin r) (k : Fin (m + (q + 1) + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k =
      (-1 : ℤ) ^ ((s.vertical k).val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank v (s.horizontal k)) := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_vertex_active_or_incoming s v k hk with hc | ⟨e, he, hnot⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ hc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_label]
  · have hs := (s.step_of_notMem e hnot).1
    rw [he] at hs
    have hcolor : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v e.castSucc = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v k := congrArg v hs.symm
    have hbase := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletionCoefficient_eq_rank_of_adjacent (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) e.castSucc k
      (congrArg (fun j : Fin (m + (q + 1) + 1) => j.val) he.symm) hcolor
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_label] at hbase
    exact hbase

/-- C233：垂直頂点の指定色の出力次数は正。 -/
lemma outputDegree_pos_vertical {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + (q + 1) + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical) :
    0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_vertex_active_or_incoming s v.val k hk with hc | ⟨e, he, hnot⟩
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_active s v k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  · have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_after_vertical s v e hnot
    simpa only [he] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
