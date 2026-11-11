module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinateCases
/-!
概要：混合成分の削除と左右切断を、元の単体とパラメーターの有限集合で計算する。
方針：任意の頂点を左右に分け、所属と区間の順序を比較する。
規約：部分集合や切断点の非空性を仮定せずに成立する集合の等式を使う。
使われ方：HA の削除項と切断合成を、回収した Hom の成分へ移す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarJoinSubset_erase_left {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).erase (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.erase j) L := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_erase, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left]
    exact and_congr (not_congr (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective n m).eq_iff) Iff.rfl
  · intro i
    simp only [Finset.mem_erase, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right]
    exact and_iff_right (Ne.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_ne_right j i))

lemma dgCoherentBarJoinSubset_erase_right {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).erase (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (L.erase j) := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_erase, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left]
    exact and_iff_right (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_ne_right i j)
  · intro i
    simp only [Finset.mem_erase, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right]
    exact and_congr (not_congr (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective n m).eq_iff) Iff.rfl

lemma dgCoherentBarJoinSubset_filter_le_left {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).filter (· ≤ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j) =
      (K.filter (· ≤ j)).image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_mem_image, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_le_left]
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_not_mem_left_image]
    exact iff_false_intro (fun h => (not_le.mpr
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right j i)) h.2)

lemma dgCoherentBarJoinSubset_filter_left_le {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).filter (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j ≤ ·) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (K.filter (j ≤ ·)) L := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_le_left]
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right]
    exact and_iff_left (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right j i).le

lemma dgCoherentBarJoinSubset_filter_le_right {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).filter (· ≤ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K (L.filter (· ≤ j)) := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left]
    exact and_iff_left (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right i j).le
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_le_right]

lemma dgCoherentBarJoinSubset_filter_right_le {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).filter (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j ≤ ·) =
      (L.filter (j ≤ ·)).image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) := by
  apply Finset.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_not_mem_right_image]
    exact iff_false_intro (fun h => (not_le.mpr
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_lt_right i j)) h.2)
  · intro i
    simp only [Finset.mem_filter, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_mem_image, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_le_right]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
