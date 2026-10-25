module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaces
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
/-!
概要：逆構成の純粋な右成分を、定値終点単体の成分へ戻す。
方針：左右の面の制限を単射成分比較へ適用する。
規約：任意の線形成分族に成立する。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_pure_right_hom_heq {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌)
    (L : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (Index.nonempty hL))
    (hb : b = L.max' (Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ)) :
    HEq ((dgCoherentBarInverseRawData R D F hMC N f s).hom
      (L.image (dgCoherentBarJoinRight n m))
      (dgCoherentBarJoinRight n m a) (dgCoherentBarJoinRight n m b) k
      (Index.image_two (dgCoherentBarJoinRight_injective n m).injOn hL)
      (Index.image_min (dgCoherentBarJoinRight n m).monotone
        (by rw [ha]; exact L.isLeast_min' _) _)
      (Index.image_max (dgCoherentBarJoinRight n m).monotone
        (by rw [hb]; exact L.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (dgCoherentBarJoinRight_injective n m)];
          exact hk))
      ((InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) N) m).hom L a b k hL ha hb hk) := by
  have h := dgCoherentBarInverseRawData_right R D F hMC N f s
  have hh := SimplexData.hom_heq_of_eq h L a b k hL ha hb hk
  change HEq (((dgCoherentBarInverseRawData R D F hMC N f s).pullback
    (dgCoherentBarJoinRight n m)).hom L a b k hL ha hb hk) _ at hh
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarJoinRight_injective n m).injOn] at hh
  exact hh

end SerrePositivity.InfinityCategories
