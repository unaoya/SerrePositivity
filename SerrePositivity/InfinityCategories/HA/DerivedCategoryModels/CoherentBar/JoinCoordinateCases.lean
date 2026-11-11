module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinSplitIndex
/-!
概要：join の任意の頂点を左右の区間に分け、部分集合の所属を計算する。
方針：区間の値の範囲と、左右への分割の逆写像を使う。
規約：空の部分集合を含む。
使われ方：HA の削除と左右切断の有限集合の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarJoin_cases {n m : ℕ} {P : Fin (n + m + 1 + 1) → Prop}
    (hl : ∀ i, P (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i))
    (hr : ∀ j, P (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j)) : ∀ x, P x := by
  intro x
  by_cases hx : x.val < n + 1
  · have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m ⟨x.val, hx⟩ = x := Fin.ext rfl
    exact he ▸ hl ⟨x.val, hx⟩
  · let j : Fin (m + 1) := ⟨x.val - (n + 1), by have := x.isLt; omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j = x := Fin.ext (by
      change n + 1 + (x.val - (n + 1)) = x.val
      omega)
    exact he ▸ hr j

@[simp] lemma dgCoherentBarJoinSubset_mem_left {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L ↔ i ∈ K := by
  have h := Finset.ext_iff.mp (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart_subset K L) i
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart, Finset.mem_filter, Finset.mem_univ, true_and] using h

@[simp] lemma dgCoherentBarJoinSubset_mem_right {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L ↔ j ∈ L := by
  have h := Finset.ext_iff.mp (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart_subset K L) j
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart, Finset.mem_filter, Finset.mem_univ, true_and] using h

@[simp] lemma dgCoherentBarJoinLeft_mem_image {n m : ℕ}
    (K : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ∈ K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) ↔ i ∈ K := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using
    dgCoherentBarJoinSubset_mem_left K (∅ : Finset (Fin (m + 1))) i

@[simp] lemma dgCoherentBarJoinRight_mem_image {n m : ℕ}
    (L : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j ∈ L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) ↔ j ∈ L := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using
    dgCoherentBarJoinSubset_mem_right (∅ : Finset (Fin (n + 1))) L j

@[simp] lemma dgCoherentBarJoinLeft_not_mem_right_image {n m : ℕ}
    (L : Finset (Fin (m + 1))) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ∉ L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union,
    Finset.notMem_empty, iff_false] using
    dgCoherentBarJoinSubset_mem_left (∅ : Finset (Fin (n + 1))) L i

@[simp] lemma dgCoherentBarJoinRight_not_mem_left_image {n m : ℕ}
    (K : Finset (Fin (n + 1))) (j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j ∉ K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty,
    Finset.notMem_empty, iff_false] using
    dgCoherentBarJoinSubset_mem_right K (∅ : Finset (Fin (m + 1))) j

@[simp] lemma dgCoherentBarJoinLeft_le_left {n m : ℕ} (i j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i ≤ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j ↔ i ≤ j := Iff.rfl

@[simp] lemma dgCoherentBarJoinRight_le_right {n m : ℕ} (i j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m i ≤ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j ↔ i ≤ j := by
  change n + 1 + i.val ≤ n + 1 + j.val ↔ i.val ≤ j.val
  omega

lemma dgCoherentBarJoinLeft_lt_right {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i < _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m j := by
  change i.val < n + 1 + j.val
  have := i.isLt
  omega

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
