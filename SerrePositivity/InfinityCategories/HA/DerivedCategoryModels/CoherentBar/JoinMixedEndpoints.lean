module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinateCases
/-!
概要：混合部分集合の両端点と、左右の対象族を連結した対象族を計算する。
方針：左右の区間の厳密な順序を使い、最小・最大の特徴付けを適用する。
規約：両側の集合は非空とし、方程式を仮定しない。
使われ方：逆比較の混合 cochain の実端点への輸送。
-/
@[expose] public section
noncomputable section
universe v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarJoinSubset_min {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hJ : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).Nonempty) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' hJ =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m (K.min' hK) := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  constructor
  · exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left K L _).mpr (K.min'_mem hK)
  · intro b hb
    rcases Finset.mem_union.mp hb with hl | hr
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_le_left _ _).mpr (K.min'_le i hi)
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
      exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right _ j).le

lemma dgCoherentBarJoinSubset_max {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hL : L.Nonempty) (hJ : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).Nonempty) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' hJ =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m (L.max' hL) := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right K L _).mpr (L.max'_mem hL)
  · intro b hb
    rcases Finset.mem_union.mp hb with hl | hr
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right i _).le
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_le_right _ _).mpr (L.le_max' j hj)

def dgCoherentBarJoinObjects {C : Type v} {n m : ℕ}
    (s : Fin (n + 1) → C) (t : Fin (m + 1) → C) (i : Fin (n + m + 1 + 1)) : C :=
  if h : i.val < n + 1 then s ⟨i.val, h⟩
  else t ⟨i.val - (n + 1), by have := i.isLt; omega⟩

@[simp] lemma dgCoherentBarJoinObjects_left {C : Type v} {n m : ℕ}
    (s : Fin (n + 1) → C) (t : Fin (m + 1) → C) (i : Fin (n + 1)) :
    dgCoherentBarJoinObjects s t (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i) = s i := by
  unfold dgCoherentBarJoinObjects
  rw [dite_eq_left (show (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i).val < n + 1 from i.isLt)]
  congr 1

@[simp] lemma dgCoherentBarJoinObjects_right {C : Type v} {n m : ℕ}
    (s : Fin (n + 1) → C) (t : Fin (m + 1) → C) (j : Fin (m + 1)) :
    dgCoherentBarJoinObjects s t (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j) = t j := by
  unfold dgCoherentBarJoinObjects
  rw [dite_eq_right (show ¬ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j).val < n + 1 by
    change ¬ n + 1 + j.val < n + 1; omega)]
  congr 1
  apply Fin.ext
  change n + 1 + j.val - (n + 1) = j.val
  omega

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
