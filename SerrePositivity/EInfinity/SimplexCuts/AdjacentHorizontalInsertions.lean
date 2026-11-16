module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalDeletion
public import SerrePositivity.EInfinity.SimplexCuts.Expanded

/-!
# 同じ水平辺の前後への挿入は同じCut

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の既存構成の法則、報告 §320。
元の有限辺集合の同方向の二辺を保ち、同じ挿入の定義で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元から属する辺の前後へ重ねて挿入した辺集合は同じ（BF §1.1.3）。 -/
lemma insertPosition_adjacent_of_mem {N : ℕ} (S : Finset (Fin N)) (a : Fin N) (ha : a ∈ S) :
    BarrattEccles.insertPosition S a.castSucc = BarrattEccles.insertPosition S a.succ := by
  have hf (j : Fin N) (hj : j ∈ S.erase a) : a.castSucc.succAbove j = a.succ.succAbove j := by
    have hne := (Finset.mem_erase.mp hj).1
    have hn : j.val ≠ a.val := fun he => hne (Fin.ext he)
    simp only [Fin.succAbove]
    split_ifs <;> try rfl
    all_goals
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at *
      omega
  have hm : (S.erase a).map (Fin.succAboveOrderEmb a.castSucc).toEmbedding =
      (S.erase a).map (Fin.succAboveOrderEmb a.succ).toEmbedding := by
    ext b
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨j, hj, he⟩
      exact ⟨j, hj, (hf j hj).symm.trans he⟩
    · rintro ⟨j, hj, he⟩
      exact ⟨j, hj, (hf j hj).trans he⟩
  unfold BarrattEccles.insertPosition
  rw [← Finset.insert_erase ha, Finset.map_insert, Finset.map_insert]
  change insert a.castSucc (insert (a.castSucc.succAbove a)
      ((S.erase a).map (Fin.succAboveOrderEmb a.castSucc).toEmbedding)) =
    insert a.succ (insert (a.succ.succAbove a)
      ((S.erase a).map (Fin.succAboveOrderEmb a.succ).toEmbedding))
  rw [Fin.succAbove_castSucc_self, Fin.succAbove_succ_self, hm, Finset.insert_comm]

/-- 元の水平辺の前後への同方向挿入は、同じCutそのもの（BF §1.1.3）。 -/
lemma horizontalInsertionEquiv_adjacent_of_mem {m q : ℕ} (t : Cut m q)
    (a : Fin (m + q)) (ha : a ∈ t.val) :
    (BarrattEccles.horizontalInsertionEquiv m q (Fin.cast (by omega) a.castSucc) t).val =
      (BarrattEccles.horizontalInsertionEquiv m q (Fin.cast (by omega) a.succ) t).val := by
  apply Subtype.ext
  change (BarrattEccles.insertPosition t.val a.castSucc).map
      (finCongr (show m + q + 1 = m + 1 + q by omega)).toEmbedding =
    (BarrattEccles.insertPosition t.val a.succ).map
      (finCongr (show m + q + 1 = m + 1 + q by omega)).toEmbedding
  rw [insertPosition_adjacent_of_mem t.val a ha]

end SerrePositivity.EInfinity.SimplexCuts
