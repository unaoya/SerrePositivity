module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubset
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterDegeneracies
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ParameterSubsetLabels
/-!
概要：右部分集合から回収する Hom は、全パラメーター写像に自然である。
方針：局所単射の場合は実部分単体のラベルを照合し、非単射の場合は退化消滅を使う。
規約：終域は実最大頂点のまま異種等号で保持する。
使われ方：回収した一点下のデータの全面・全退化での自然性。
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

lemma dgCoherentBarCoconeLiftSubsetHom_map_of_injOn {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) J k hJ hk)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c (J.image α) k (hJ.image α)
        (by rw [Finset.card_image_of_injOn hi]; exact hk)) := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hcI : (J.image α).card = r + 1 := by rw [Finset.card_image_of_injOn hi]; exact hc
  have hLabel := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_map_of_injOn c α J hi r hc
  have hPhi := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom_heq_of_index_eq R D F hMC _ _ hLabel
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) J k hJ hk hc).trans
    (hPhi.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC c (J.image α) k
      (hJ.image α) (by rw [Finset.card_image_of_injOn hi]; exact hk) hcI).symm)

lemma dgCoherentBarCoconeLiftSubsetHom_map_of_not_injOn {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬Set.InjOn α (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) J k hJ hk = 0 := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hDeg := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_degenerate_of_not_injOn c α J hi r hc
  have hPhi : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom_degenerate R D F hMC
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) J r hc, hDeg⟩
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom
  rw [hPhi]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarGradedTransport_zero R D rfl _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
