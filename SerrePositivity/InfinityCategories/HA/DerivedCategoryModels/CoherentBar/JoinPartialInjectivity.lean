module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSimplices
/-!
概要：join の混合集合上の単射性を左右の単射性に分解する。
方針：左右の区間の像が交わらないことと、それぞれの包含の単射性を使う。
規約：全体での単射性は要求しない。
使われ方：逆構成の退化写像に対する自然性。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarJoinOrderMap_injOn_subset_iff {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1))) :
    Set.InjOn (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set (Fin (a + b + 1 + 1))) ↔
    Set.InjOn α (K : Set (Fin (a + 1))) ∧ Set.InjOn β (L : Set (Fin (b + 1))) := by
  constructor
  · intro h
    constructor
    · intro i hi j hj hij
      apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective a b
      apply h ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left K L i).mpr hi)
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_left K L j).mpr hj)
      rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left, hij]
    · intro i hi j hj hij
      apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective a b
      apply h ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right K L i).mpr hi)
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_mem_right K L j).mpr hj)
      rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right, hij]
  · rintro ⟨hK, hL⟩ x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left] at hxy
        exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft a b)
          (hK hi hj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective n m hxy))
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right] at hxy
        exact False.elim (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_ne_right (α i) (β j) hxy)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left] at hxy
        exact False.elim (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_ne_right (α j) (β i) hxy.symm)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right] at hxy
        exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight a b)
          (hL hi hj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective n m hxy))

lemma dgCoherentBarJoinSubset_card_ne_two_of_not_injOn {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (hi : ¬ Set.InjOn (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set (Fin (a + b + 1 + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card ≠ 2 := by
  intro hc
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card] at hc
  have hpK := Finset.card_pos.mpr hK
  have hpL := Finset.card_pos.mpr hL
  have hK1 : K.card ≤ 1 := by omega
  have hL1 : L.card ≤ 1 := by omega
  apply hi
  apply (dgCoherentBarJoinOrderMap_injOn_subset_iff α β K L).mpr
  exact ⟨fun i hi j hj _ => Finset.card_le_one.mp hK1 i hi j hj,
    fun i hi j hj _ => Finset.card_le_one.mp hL1 i hi j hj⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
