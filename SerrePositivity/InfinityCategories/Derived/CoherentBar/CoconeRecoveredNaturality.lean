module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredVanishing
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_map {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c) =
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α) := by
  classical
  apply dgCoherentBarJoinSimplexData_ext
  · exact dgCoherentBarCoconeRecoveredRawData_map_left R D F hMC c α
  · exact dgCoherentBarCoconeRecoveredRawData_map_right R D F hMC c α
  · intro K L hK hL a b k hJ ha hb hk
    by_cases hiL : Set.InjOn α (L : Set (Fin (m + 1)))
    · exact dgCoherentBarCoconeRecoveredRawData_map_mixed_of_injOn R D F hMC c α
        K L hK hL hiL a b k hJ ha hb hk
    · have hi : ¬Set.InjOn (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)
          ((dgCoherentBarJoinSubset K L) : Set (Fin (0 + m + 1 + 1))) := by
        intro h
        exact hiL ((dgCoherentBarJoinOrderMap_injOn_subset_iff
          (OrderHom.id : Fin 1 →o Fin 1) α K L).mp h).2
      rw [dgCoherentBarCoconeRecoveredRawData_mixed_zero_of_not_injOn R D F hMC c α
        K L hK hL hiL a b k hJ ha hb hk,
        SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi
          (dgCoherentBarJoinSubset_card_ne_two_of_not_injOn
            (OrderHom.id : Fin 1 →o Fin 1) α K L hK hL hi)]
      exact gradedHom_zero_heq (A := R) (D := RightModule R D)
        (dgCoherentBarCoconeRecoveredRawData_map_obj R D F hMC c α a)
        (dgCoherentBarCoconeRecoveredRawData_map_obj R D F hMC c α b) rfl

end SerrePositivity.InfinityCategories
