module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHomEquation
/-!
概要：回収した一点下のデータの削除と左切断は、型付きの回収 Hom に一致する。
方針：左右の部分集合を直接計算し、join の混合成分の輸送を消す。
規約：回収データの HA 方程式はまだ仮定しない。
使われ方：回収 Hom の実微分式を一点下の HA 方程式へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredFullErase_parameter {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullErase (dgCoherentBarCoconeRecoveredRawData R D F hMC c)
      (j.natAdd 0)) (dgCoherentBarCoconeLiftParameterErase R D F hMC c j) := by
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c
  let L : Finset (Fin (m + 2)) := Finset.univ.erase j.castSucc
  let S := dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L
  have hj : dgCoherentBarJoinRight 0 (m + 1) j.castSucc =
      (j.natAdd 0).succ.castSucc := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hSet : S = (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).erase
      (j.natAdd 0).succ.castSucc := by
    change dgCoherentBarJoinSubset Finset.univ (Finset.univ.erase j.castSucc) = _
    rw [← dgCoherentBarJoinSubset_erase_right, dgCoherentBarJoinSubset_univ, hj]
  have hS : 2 ≤ S.card := by
    dsimp only [S, L]
    rw [dgCoherentBarJoinSubset_card]
    simp
    omega
  have ha : (0 : Fin (0 + (m + 1) + 2)) = S.min' (Index.nonempty hS) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_erase.mpr
      ⟨ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos (j.natAdd 0))),
        Finset.mem_univ _⟩
  have hb : Fin.last (0 + (m + 1) + 1) = S.max' (Index.nonempty hS) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩
    · exact Fin.le_last _
  have hk : -(m : ℤ) = 2 - (S.card : ℤ) := by
    dsimp only [S, L]
    rw [dgCoherentBarJoinSubset_card]
    simp
    omega
  have hMixed := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c L
    (dgCoherentBarParameterErase_nonempty j) 0 (Fin.last (0 + (m + 1) + 1))
    (-(m : ℤ)) hS ha hb hk
  have hErase : HEq (dgCoherentBarCoconeLiftParameterErase R D F hMC c j)
      (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(m : ℤ))
        (dgCoherentBarParameterErase_nonempty j) (by simp [L])) := by
    unfold dgCoherentBarCoconeLiftParameterErase
    exact gradedHomTransport_heq _ _ _ _
  refine HEq.trans ?_ (hMixed.trans hErase.symm)
  exact SimplexData.hom_heq_of_indices_degree Q hSet.symm rfl rfl (by omega)

lemma dgCoherentBarCoconeRecoveredFullLeft_parameter {m : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullLeft (dgCoherentBarCoconeRecoveredRawData R D F hMC c)
      (j.natAdd 0)) (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j) := by
  let Q := dgCoherentBarCoconeRecoveredRawData R D F hMC c
  let L := dgCoherentBarParameterPrefix j
  let S := dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L
  let v := (j.natAdd 0).succ.castSucc
  have hj : dgCoherentBarJoinRight 0 (m + 1) j.castSucc = v := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hSet : S = (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter (· ≤ v) := by
    have h := dgCoherentBarJoinSubset_filter_le_right
      (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hS : 2 ≤ S.card := by
    dsimp only [S, L]
    rw [dgCoherentBarJoinSubset_card, dgCoherentBarParameterPrefix_card]
    simp
    omega
  have ha : (0 : Fin (0 + (m + 1) + 2)) = S.min' (Index.nonempty hS) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have hb : v = S.max' (Index.nonempty hS) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
    · apply Finset.max'_le
      intro x hx
      rw [hSet] at hx
      exact (Finset.mem_filter.mp hx).2
  have hk : -(j.val : ℤ) = 2 - (S.card : ℤ) := by
    dsimp only [S, L]
    rw [dgCoherentBarJoinSubset_card, dgCoherentBarParameterPrefix_card]
    simp
    omega
  have hMixed := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c L
    (dgCoherentBarParameterPrefix_nonempty j) 0 v (-(j.val : ℤ)) hS ha hb hk
  have hPrefix : HEq (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
      (dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
        (dgCoherentBarParameterPrefix_nonempty j)
        (by rw [dgCoherentBarParameterPrefix_card]; push_cast; omega)) := by
    unfold dgCoherentBarCoconeLiftParameterPrefix
    exact gradedHomTransport_heq _ _ _ _
  have hd : (2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
      (· ≤ v)).card : ℤ)) = -(j.val : ℤ) := by
    rw [← hSet]
    exact hk.symm
  refine HEq.trans ?_ (hMixed.trans hPrefix.symm)
  exact SimplexData.hom_heq_of_indices_degree Q hSet.symm rfl rfl hd

end SerrePositivity.InfinityCategories
