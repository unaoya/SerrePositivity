module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubsetNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaceNaturality
/-!
概要：回収した一点下のデータの二つの純粋面と全対象は、パラメーター変更に自然である。
方針：join の左右包含との可換性と元の coslice 射影の自然性を使う。
規約：単射性を仮定しない。
使われ方：回収データ全体の全面・全退化での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarFinOneSubset_eq_univ (K : Finset (Fin 1)) (hK : K.Nonempty) :
    K = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  obtain ⟨j, hj⟩ := hK
  have h : i = j := Subsingleton.elim _ _
  rwa [h]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_map_left {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).pullback (dgCoherentBarJoinLeft 0 m) =
    ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)).pullback
        (dgCoherentBarJoinLeft 0 m) := by
  rw [dgCoherentBarJoin_pullback_left, dgCoherentBarCoconeRecoveredRawData_left,
    dgCoherentBarCoconeRecoveredRawData_left, SimplexData.pullback_id]

lemma dgCoherentBarCoconeRecoveredRawData_map_right {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).pullback (dgCoherentBarJoinRight 0 m) =
    ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)).pullback
        (dgCoherentBarJoinRight 0 m) := by
  rw [dgCoherentBarJoin_pullback_right, dgCoherentBarCoconeRecoveredRawData_right,
    dgCoherentBarCoconeRecoveredRawData_right]
  exact congrArg Simplex.toSimplexData
    ((sliceUnderProjection F).naturality_apply (SimplexCategory.mkHom α).op c)

lemma dgCoherentBarCoconeRecoveredRawData_map_obj {m n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1))
    (i : Fin (0 + m + 1 + 1)) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).obj i =
    ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)).obj i := by
  refine dgCoherentBarJoin_cases (n := 0) (m := m) (P := fun j =>
    (dgCoherentBarCoconeRecoveredRawData R D F hMC
      ((sliceUnder F).map (SimplexCategory.mkHom α).op c)).obj j =
    ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
      (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α)).obj j) ?_ ?_ i
  · intro j
    exact congrArg (fun t : SimplexData R (RightModule R D) 0 => t.obj j)
      (dgCoherentBarCoconeRecoveredRawData_map_left R D F hMC c α)
  · intro j
    exact congrArg (fun t : SimplexData R (RightModule R D) m => t.obj j)
      (dgCoherentBarCoconeRecoveredRawData_map_right R D F hMC c α)

end SerrePositivity.InfinityCategories
