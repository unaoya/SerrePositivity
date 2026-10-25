module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
/-!
概要：回収した一点下のデータの純粋右成分は、元の右面の実 HA 成分に一致する。
方針：左右の面の制限を単射成分比較へ適用する。
規約：回収データの HA 方程式は仮定しない。
使われ方：パラメーター側の HA 切断合成の比較。
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

lemma dgCoherentBarCoconeRecoveredRawData_pure_right_hom_heq {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌)
    (L : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (Index.nonempty hL))
    (hb : b = L.max' (Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ)) :
    HEq ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom
      (L.image (dgCoherentBarJoinRight 0 m))
      (dgCoherentBarJoinRight 0 m a) (dgCoherentBarJoinRight 0 m b) k
      (Index.image_two (dgCoherentBarJoinRight_injective 0 m).injOn hL)
      (Index.image_min (dgCoherentBarJoinRight 0 m).monotone
        (by rw [ha]; exact L.isLeast_min' _) _)
      (Index.image_max (dgCoherentBarJoinRight 0 m).monotone
        (by rw [hb]; exact L.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (dgCoherentBarJoinRight_injective 0 m)];
          exact hk))
      (((sliceUnderProjection F).app (Opposite.op ⦋m⦌) c).hom L a b k hL ha hb hk) := by
  have h := dgCoherentBarCoconeRecoveredRawData_right R D F hMC c
  have hh := SimplexData.hom_heq_of_eq h L a b k hL ha hb hk
  change HEq (((dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback
    (dgCoherentBarJoinRight 0 m)).hom L a b k hL ha hb hk) _ at hh
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarJoinRight_injective 0 m).injOn] at hh
  exact hh

end SerrePositivity.InfinityCategories
