module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearReindex
/-!
概要：回収した右 pinched 成分族は、全パラメーター写像による引き戻しに自然である。
方針：部分集合上の単射分岐ではラベルの等式、非単射分岐では退化消滅を使う。
規約：線形方程式の成立を先取りせず、成分族の段階で自然性を証明する。
使われ方：写像空間の逆比較を全ての面・退化と可換な射にする。
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
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeSubsetHom_map_of_injOn {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom R D F hMC y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom R D F hMC y c (J.image α) k (hJ.image α)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hcI : (J.image α).card = r + 1 := by rw [Finset.card_image_of_injOn hi]; exact hc
  have hLabel := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_map_of_injOn c α J hi r hc
  have hPhi : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y c (J.image α) r hcI) :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom_heq_of_index_eq R D F hMC y _ _ hLabel
  have hScalar := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    rfl rfl rfl (r : ℤ).negOnePow _ _ hPhi
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk r hc).trans
    (hScalar.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y c (J.image α) k
      (hJ.image α) (by rw [Finset.card_image_of_injOn hi]; exact hk) r hcI).symm))

lemma dgCoherentBarCoconeSubsetHom_map_of_not_injOn {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬Set.InjOn α (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom R D F hMC y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk = 0 := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hDeg := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_degenerate_of_not_injOn c α J hi r hc
  have hPhi : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc = 0 :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom_degenerate R D F hMC y
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J r hc, hDeg⟩
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom
  rw [hPhi, smul_zero]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarGradedTransport_zero R D rfl rfl _

lemma dgCoherentBarCoconeLinearData_map {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom R D F hMC y
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c)).component J k hJ hk
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj α _ J k hJ hk hi]
    exact dgCoherentBarCoconeSubsetHom_map_of_injOn R D F hMC y c α J k hJ hk hi
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj α _ J k hJ hk hi]
    exact dgCoherentBarCoconeSubsetHom_map_of_not_injOn R D F hMC y c α J k hJ hk hi

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
