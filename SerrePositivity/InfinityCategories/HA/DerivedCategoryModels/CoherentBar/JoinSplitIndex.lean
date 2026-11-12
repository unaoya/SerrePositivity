module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinMixedIndex
/-!
概要：join の任意の成分添字を左右の区間へ分け、その和集合を回収する。
方針：左右の包含の逆像を有限集合として取り、区間の交わらなさを使う。
規約：片側が空の添字も含む。
使われ方：任意の HA 成分を純粋な面または混合部分集合として分類する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarJoinLeft_ne_right {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ≠ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = n + 1 + j.val at hv
  have := i.isLt
  omega

def dgCoherentBarJoinLeftPart (n m : ℕ) (J : Finset (Fin (n + m + 1 + 1))) :
    Finset (Fin (n + 1)) := Finset.univ.filter (fun i => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ∈ J)

def dgCoherentBarJoinRightPart (n m : ℕ) (J : Finset (Fin (n + m + 1 + 1))) :
    Finset (Fin (m + 1)) := Finset.univ.filter (fun i => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m i ∈ J)

lemma dgCoherentBarJoinLeftPart_subset {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) :
    dgCoherentBarJoinLeftPart n m (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) = K := by
  ext i
  simp only [dgCoherentBarJoinLeftPart, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hl | hr
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hl
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective n m hji ▸ hj
    · obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hr
      exact False.elim (dgCoherentBarJoinLeft_ne_right i j hji.symm)
  · intro hi
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

lemma dgCoherentBarJoinRightPart_subset {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) :
    dgCoherentBarJoinRightPart n m (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) = L := by
  ext i
  simp only [dgCoherentBarJoinRightPart, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hl | hr
    · obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hl
      exact False.elim (dgCoherentBarJoinLeft_ne_right j i hji)
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hr
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective n m hji ▸ hj
  · intro hi
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

lemma dgCoherentBarJoinSubset_parts (n m : ℕ) (J : Finset (Fin (n + m + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (dgCoherentBarJoinLeftPart n m J)
      (dgCoherentBarJoinRightPart n m J) = J := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hl | hr
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
      exact (Finset.mem_filter.mp hj).2
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_filter.mp hj).2
  · intro hi
    by_cases hil : i.val < n + 1
    · let j : Fin (n + 1) := ⟨i.val, hil⟩
      have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j = i := Fin.ext rfl
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, he.symm ▸ hi⟩, he⟩
    · let j : Fin (m + 1) := ⟨i.val - (n + 1), by have := i.isLt; omega⟩
      have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j = i := Fin.ext (by
        change n + 1 + (i.val - (n + 1)) = i.val
        omega)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, he.symm ▸ hi⟩, he⟩

lemma dgCoherentBarJoinParts_card (n m : ℕ) (J : Finset (Fin (n + m + 1 + 1))) :
    (dgCoherentBarJoinLeftPart n m J).card + (dgCoherentBarJoinRightPart n m J).card =
      J.card := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, dgCoherentBarJoinSubset_parts]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
