module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinNaturality
/-!
概要：join の混合 HA 成分の添字を、左右の非空部分集合で表示する。
方針：左右の区間への像は交わらないことを使い、濃度と添字作用を計算する。
規約：元の単体とパラメーターの区間を保持する。
使われ方：高次余錐族の全混合成分の回収と微分方程式の二つの区間への分割。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgCoherentBarJoinLeft_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) := by
  intro i j h
  have hv : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m i).val = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m j).val :=
    congrArg Fin.val h
  exact Fin.ext hv

lemma dgCoherentBarJoinRight_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) := by
  intro i j h
  have hv := congrArg Fin.val h
  change n + 1 + i.val = n + 1 + j.val at hv
  exact Fin.ext (Nat.add_left_cancel hv)

def dgCoherentBarJoinSubset {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) :
    Finset (Fin (n + m + 1 + 1)) :=
  K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) ∪ L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m)

lemma dgCoherentBarJoinSubset_disjoint {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) :
    Disjoint (K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m))
      (L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
  have hv := congrArg Fin.val hj
  change n + 1 + j.val = i.val at hv
  have := i.isLt
  omega

lemma dgCoherentBarJoinSubset_card {n m : ℕ}
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))) :
    (dgCoherentBarJoinSubset K L).card = K.card + L.card := by
  rw [dgCoherentBarJoinSubset, Finset.card_union_of_disjoint
    (dgCoherentBarJoinSubset_disjoint K L),
    Finset.card_image_of_injective _ (dgCoherentBarJoinLeft_injective n m),
    Finset.card_image_of_injective _ (dgCoherentBarJoinRight_injective n m)]

lemma dgCoherentBarJoinSubset_univ (n m : ℕ) :
    dgCoherentBarJoinSubset (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 1))) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [dgCoherentBarJoinSubset_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

lemma dgCoherentBarJoinSubset_map {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1))) :
    (dgCoherentBarJoinSubset K L).image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β) =
      dgCoherentBarJoinSubset (K.image α) (L.image β) := by
  unfold dgCoherentBarJoinSubset
  rw [Finset.image_union]
  congr 1
  · rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_left α β i
  · rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_right α β i

lemma dgCoherentBarJoinOrderMap_injective {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  by_cases hi : i.val < a + 1 <;> by_cases hj : j.val < a + 1
  · simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap, OrderHom.coe_mk, hi, hj, dite_true,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom] at hv
    change (α ⟨i.val, hi⟩).val = (α ⟨j.val, hj⟩).val at hv
    exact congrArg (fun z : Fin (a + 1) => z.val) (hα (Fin.ext hv))
  · have hei := (α ⟨i.val, hi⟩).isLt
    simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap, OrderHom.coe_mk, hi, hj, dite_true, dite_false,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom] at hv
    omega
  · have hej := (α ⟨j.val, hj⟩).isLt
    simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap, OrderHom.coe_mk, hi, hj, dite_true, dite_false,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom] at hv
    omega
  · simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap, OrderHom.coe_mk, hi, hj, dite_false,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom] at hv
    have hiv : i.val - (a + 1) < b + 1 := by have := i.isLt; omega
    have hjv : j.val - (a + 1) < b + 1 := by have := j.isLt; omega
    change n + 1 + (β ⟨i.val - (a + 1), hiv⟩).val =
      n + 1 + (β ⟨j.val - (a + 1), hjv⟩).val at hv
    have he := congrArg Fin.val (hβ (Fin.ext (Nat.add_left_cancel hv)))
    change i.val - (a + 1) = j.val - (a + 1) at he
    omega

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
