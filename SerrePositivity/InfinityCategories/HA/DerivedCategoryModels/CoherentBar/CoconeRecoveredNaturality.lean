module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredVanishing
/-!
概要：回収した一点下のデータは全パラメーター写像に厳密に自然である。
方針：純粋面と混合成分で比較し、局所単射分岐と退化分岐を合わせる。
規約：全ての面・退化と一般の単調写像を含む。
使われ方：全部分集合の HA 方程式の移送と native 余錐の標準族の比較。
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

lemma dgCoherentBarCoconeRecoveredRawData_map {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α) := by
  classical
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSimplexData_ext
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map_left R D F hMC c α
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map_right R D F hMC c α
  · intro K L hK hL a b k hJ ha hb hk
    by_cases hiL : Set.InjOn α (L : Set (Fin (m + 1)))
    · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map_mixed_of_injOn R D F hMC c α
        K L hK hL hiL a b k hJ ha hb hk
    · have hi : ¬Set.InjOn (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)
          ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set (Fin (0 + m + 1 + 1))) := by
        intro h
        exact hiL ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_injOn_subset_iff
          (OrderHom.id : Fin 1 →o Fin 1) α K L).mp h).2
      rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_mixed_zero_of_not_injOn R D F hMC c α
        K L hK hL hiL a b k hJ ha hb hk,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card_ne_two_of_not_injOn
            (OrderHom.id : Fin 1 →o Fin 1) α K L hK hL hi)]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map_obj R D F hMC c α a)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map_obj R D F hMC c α b) rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
