module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaces
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
/-!
概要：逆構成の純粋な左成分を、同じ native 単体の成分へ戻す。
方針：左右の面の制限を単射成分比較へ適用する。
規約：任意の線形成分族に成立する。
使われ方：元の単体側の HA 切断合成の比較。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_pure_left_hom_heq {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hK : 2 ≤ K.card) (ha : a = K.min' (Index.nonempty hK))
    (hb : b = K.max' (Index.nonempty hK)) (hk : k = 2 - (K.card : ℤ)) :
    HEq ((dgCoherentBarInverseRawData R D F hMC N f s).hom
      (K.image (dgCoherentBarJoinLeft n m))
      (dgCoherentBarJoinLeft n m a) (dgCoherentBarJoinLeft n m b) k
      (Index.image_two (dgCoherentBarJoinLeft_injective n m).injOn hK)
      (Index.image_min (dgCoherentBarJoinLeft n m).monotone
        (by rw [ha]; exact K.isLeast_min' _) _)
      (Index.image_max (dgCoherentBarJoinLeft n m).monotone
        (by rw [hb]; exact K.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (dgCoherentBarJoinLeft_injective n m)];
          exact hk))
      ((dgCoherentBarNativeSimplex R D F hMC s).hom (K.image Fin.castSucc)
        a.castSucc b.castSucc k (Index.image_two (Fin.castSucc_injective _).injOn hK)
        (Index.image_min Fin.castSuccOrderEmb.monotone
          (by rw [ha]; exact K.isLeast_min' _) _)
        (Index.image_max Fin.castSuccOrderEmb.monotone
          (by rw [hb]; exact K.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk)) := by
  have h := (dgCoherentBarInverseRawData_left R D F hMC N f s).trans
    (congrArg DGNerve.Simplex.toSimplexData (dgCoherentBarNativeSimplex_front R D F hMC s)).symm
  exact SimplexData.hom_heq_of_pullback_eq
    (dgCoherentBarInverseRawData R D F hMC N f s)
    (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
    (dgCoherentBarJoinLeft n m) Fin.castSuccOrderEmb.toOrderHom
    h K a b k hK ha hb hk
    (dgCoherentBarJoinLeft_injective n m).injOn (Fin.castSucc_injective _).injOn


end SerrePositivity.InfinityCategories
