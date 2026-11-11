module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftHomEquation
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredFullErase_parameter {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c)
      (j.natAdd 0)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterErase R D F hMC c j) := by
  let Q := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c
  let L : Finset (Fin (m + 2)) := Finset.univ.erase j.castSucc
  let S := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 (m + 1) j.castSucc =
      (j.natAdd 0).succ.castSucc := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hSet : S = (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).erase
      (j.natAdd 0).succ.castSucc := by
    change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset Finset.univ (Finset.univ.erase j.castSucc) = _
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_erase_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj]
  have hS : 2 ≤ S.card := by
    dsimp only [S, L]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card]
    simp
    omega
  have ha : (0 : Fin (0 + (m + 1) + 2)) = S.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_erase.mpr
      ⟨ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos (j.natAdd 0))),
        Finset.mem_univ _⟩
  have hb : Fin.last (0 + (m + 1) + 1) = S.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩
    · exact Fin.le_last _
  have hk : -(m : ℤ) = 2 - (S.card : ℤ) := by
    dsimp only [S, L]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card]
    simp
    omega
  have hMixed := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c L
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterErase_nonempty j) 0 (Fin.last (0 + (m + 1) + 1))
    (-(m : ℤ)) hS ha hb hk
  have hErase : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterErase R D F hMC c j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(m : ℤ))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterErase_nonempty j) (by simp [L])) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterErase
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _
  refine HEq.trans ?_ (hMixed.trans hErase.symm)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree Q hSet.symm rfl rfl (by omega)

lemma dgCoherentBarCoconeRecoveredFullLeft_parameter {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c)
      (j.natAdd 0)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j) := by
  let Q := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix j
  let S := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L
  let v := (j.natAdd 0).succ.castSucc
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 (m + 1) j.castSucc = v := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hSet : S = (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter (· ≤ v) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_le_right
      (Finset.univ : Finset (Fin 1)) (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hS : 2 ≤ S.card := by
    dsimp only [S, L]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_card]
    simp
    omega
  have ha : (0 : Fin (0 + (m + 1) + 2)) = S.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have hb : v = S.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
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
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_card]
    simp
    omega
  have hMixed := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c L
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_nonempty j) 0 v (-(j.val : ℤ)) hS ha hb hk
  have hPrefix : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_nonempty j)
        (by rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_card]; push_cast; omega)) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _
  have hd : (2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
      (· ≤ v)).card : ℤ)) = -(j.val : ℤ) := by
    rw [← hSet]
    exact hk.symm
  refine HEq.trans ?_ (hMixed.trans hPrefix.symm)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree Q hSet.symm rfl rfl hd

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
