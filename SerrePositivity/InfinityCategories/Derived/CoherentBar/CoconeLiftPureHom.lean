module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
/-!
概要：持ち上げ余錐について、高次余錐族の純粋な左右の成分を、元の図式と実際の右面へ戻す。
方針：二つの包含に沿う制限の等式を、既存の単射成分比較へ適用する。
規約：全ての部分集合・次数を保持する。
使われ方：HA 切断合成の元の図式側の因子と、右面の HA 成分の比較。
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

lemma dgCoherentBarCoconeLiftSimplex_pure_left_hom_heq
    (hMC : dgCoherentBarMaurerCartan R D F) {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hK : 2 ≤ K.card) (ha : a = K.min' (Index.nonempty hK))
    (hb : b = K.max' (Index.nonempty hK)) (hk : k = 2 - (K.card : ℤ)) :
    HEq ((dgCoherentBarCoconeLiftSimplex R D F c s).hom
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
  have h := (dgCoherentBarCoconeLiftSimplex_left R D F c s).trans
    (dgCoherentBarNativeSimplex_front R D F hMC s).symm
  exact SimplexData.hom_heq_of_pullback_eq
    (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
    (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
    (dgCoherentBarJoinLeft n m) Fin.castSuccOrderEmb.toOrderHom
    (congrArg DGNerve.Simplex.toSimplexData h) K a b k hK ha hb hk
    (dgCoherentBarJoinLeft_injective n m).injOn (Fin.castSucc_injective _).injOn

lemma dgCoherentBarCoconeLiftSimplex_pure_right_hom_heq {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌)
    (L : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (Index.nonempty hL))
    (hb : b = L.max' (Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ)) :
    HEq ((dgCoherentBarCoconeLiftSimplex R D F c s).hom
      (L.image (dgCoherentBarJoinRight n m))
      (dgCoherentBarJoinRight n m a) (dgCoherentBarJoinRight n m b) k
      (Index.image_two (dgCoherentBarJoinRight_injective n m).injOn hL)
      (Index.image_min (dgCoherentBarJoinRight n m).monotone
        (by rw [ha]; exact L.isLeast_min' _) _)
      (Index.image_max (dgCoherentBarJoinRight n m).monotone
        (by rw [hb]; exact L.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (dgCoherentBarJoinRight_injective n m)];
          exact hk))
      (((sliceUnderProjection F).app (Opposite.op ⦋m⦌) c).hom L a b k hL ha hb hk) := by
  have h := congrArg DGNerve.Simplex.toSimplexData
    (dgCoherentBarCoconeLiftSimplex_right R D F c s)
  have hh := SimplexData.hom_heq_of_eq h L a b k hL ha hb hk
  change HEq (((dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData.pullback
    (dgCoherentBarJoinRight n m)).hom L a b k hL ha hb hk) _ at hh
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarJoinRight_injective n m).injOn] at hh
  exact hh

end SerrePositivity.InfinityCategories
