module

public import SerrePositivity.EInfinity.SimplexCuts.CaesuraVertexDeletion
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
# 単語削除後の同じ位置でのcaesura順位

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
既存の活動頂点の削除の公式と、有限接頭区間の一位置の増分を順位へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (caesura_erase_of_caesura)

/-- C133：活動頂点を削除した同じ番号での順位は、削除直前の順位。 -/
lemma caesuraRank_erase_active_at {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
    Surjection.caesuraRank (Surjection.erase v a) t = Surjection.caesuraRank v a := by
  unfold Surjection.caesuraRank
  apply Finset.card_bij (fun j _ => j.castSucc)
  · intro j hj
    have hjt := (Finset.mem_filter.mp hj).2.1
    have hjc := (Finset.mem_filter.mp hj).2.2
    have hjlt : j.castSucc < a := by
      change j.val < a.val
      change j.val < t.val at hjt
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt, ?_⟩
    have hc := (caesura_erase_of_caesura v a ha j).mp hjc
    simpa only [Fin.succAbove_of_castSucc_lt a j hjlt] using hc
  · intro j _ k _ h
    apply Fin.ext
    exact congrArg (fun z : Fin (N + 1) => z.val) h
  · intro j hj
    have hjlt := (Finset.mem_filter.mp hj).2.1
    have hjc := (Finset.mem_filter.mp hj).2.2
    have hb : j.val < N := by
      have h := t.isLt
      change j.val < a.val at hjlt
      omega
    let i : Fin N := ⟨j.val, hb⟩
    have he : i.castSucc = j := Fin.ext rfl
    have hil : i.castSucc < a := by rw [he]; exact hjlt
    have hie : a.succAbove i = j := (Fin.succAbove_of_castSucc_lt a i hil).trans he
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, he⟩
    · change j.val < t.val
      change j.val < a.val at hjlt
      omega
    · apply (caesura_erase_of_caesura v a ha i).mpr
      simpa only [hie] using hjc

/-- C134：活動頂点の単語削除係数は、削除後の同じ番号の順位でも計算できる。 -/
lemma deletionCoefficient_erase_active_rank {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (t : Fin N) (ht : t.val = a.val) :
    Surjection.deletionCoefficient v a =
      (-1 : ℤ) ^ Surjection.caesuraRank (Surjection.erase v a) t := by
  rw [Surjection.deletionCoefficient_of_caesura v a ha, caesuraRank_erase_active_at v a ha t ht]

lemma caesuraRank_eq_filter_card {N r : ℕ} (v : Fin N → Fin r) (k : Fin N) :
    Surjection.caesuraRank v k = ((caesuraPositions v).filter (fun j => j < k)).card := by
  unfold Surjection.caesuraRank
  congr 1
  ext j
  simp only [caesuraPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- C135：隣接する二位置のcaesura順位の差は、その間の一位置の活動性。 -/
lemma caesuraRank_adjacent {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) :
    Surjection.caesuraRank v b =
      Surjection.caesuraRank v a + if Surjection.Caesura v a then 1 else 0 := by
  rw [caesuraRank_eq_filter_card, caesuraRank_eq_filter_card]
  change ((caesuraPositions v).filter (fun j => j.val < b.val)).card =
    ((caesuraPositions v).filter (fun j => j.val < a.val)).card + _
  rw [hab]
  simpa only [caesuraPositions, Finset.mem_filter, Finset.mem_univ, true_and] using
    BarrattEccles.prefix_count_succ (caesuraPositions v) a

end SerrePositivity.EInfinity.SimplexCuts
