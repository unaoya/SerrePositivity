module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCoordinateCases
/-!
概要：混合成分の削除と左右切断を、元の単体とパラメーターの有限集合で計算する。
方針：任意の頂点を左右に分け、所属と区間の順序を比較する。
規約：部分集合や切断点の非空性を仮定せずに成立する集合の等式を使う。
使われ方：HA の削除項と切断合成を、回収した Hom の成分へ移す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories

lemma dgCoherentBarJoinSubset_erase_left {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (dgCoherentBarJoinSubset K L).erase (dgCoherentBarJoinLeft n m j) =
      dgCoherentBarJoinSubset (K.erase j) L := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_erase, dgCoherentBarJoinSubset_mem_left]
    exact and_congr (not_congr (dgCoherentBarJoinLeft_injective n m).eq_iff) Iff.rfl
  · intro i
    simp only [Finset.mem_erase, dgCoherentBarJoinSubset_mem_right]
    exact and_iff_right (Ne.symm (dgCoherentBarJoinLeft_ne_right j i))

lemma dgCoherentBarJoinSubset_erase_right {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (dgCoherentBarJoinSubset K L).erase (dgCoherentBarJoinRight n m j) =
      dgCoherentBarJoinSubset K (L.erase j) := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_erase, dgCoherentBarJoinSubset_mem_left]
    exact and_iff_right (dgCoherentBarJoinLeft_ne_right i j)
  · intro i
    simp only [Finset.mem_erase, dgCoherentBarJoinSubset_mem_right]
    exact and_congr (not_congr (dgCoherentBarJoinRight_injective n m).eq_iff) Iff.rfl

lemma dgCoherentBarJoinSubset_filter_le_left {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (dgCoherentBarJoinSubset K L).filter (· ≤ dgCoherentBarJoinLeft n m j) =
      (K.filter (· ≤ j)).image (dgCoherentBarJoinLeft n m) := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_left,
      dgCoherentBarJoinLeft_mem_image, dgCoherentBarJoinLeft_le_left]
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_right,
      dgCoherentBarJoinRight_not_mem_left_image]
    exact iff_false_intro (fun h => (not_le.mpr
      (dgCoherentBarJoinLeft_lt_right j i)) h.2)

lemma dgCoherentBarJoinSubset_filter_left_le {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (n + 1)) :
    (dgCoherentBarJoinSubset K L).filter (dgCoherentBarJoinLeft n m j ≤ ·) =
      dgCoherentBarJoinSubset (K.filter (j ≤ ·)) L := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_left,
      dgCoherentBarJoinLeft_le_left]
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_right]
    exact and_iff_left (dgCoherentBarJoinLeft_lt_right j i).le

lemma dgCoherentBarJoinSubset_filter_le_right {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (dgCoherentBarJoinSubset K L).filter (· ≤ dgCoherentBarJoinRight n m j) =
      dgCoherentBarJoinSubset K (L.filter (· ≤ j)) := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_left]
    exact and_iff_left (dgCoherentBarJoinLeft_lt_right i j).le
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_right,
      dgCoherentBarJoinRight_le_right]

lemma dgCoherentBarJoinSubset_filter_right_le {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    (dgCoherentBarJoinSubset K L).filter (dgCoherentBarJoinRight n m j ≤ ·) =
      (L.filter (j ≤ ·)).image (dgCoherentBarJoinRight n m) := by
  apply Finset.ext
  apply dgCoherentBarJoin_cases
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_left,
      dgCoherentBarJoinLeft_not_mem_right_image]
    exact iff_false_intro (fun h => (not_le.mpr
      (dgCoherentBarJoinLeft_lt_right i j)) h.2)
  · intro i
    simp only [Finset.mem_filter, dgCoherentBarJoinSubset_mem_right,
      dgCoherentBarJoinRight_mem_image, dgCoherentBarJoinRight_le_right]

end SerrePositivity.InfinityCategories
