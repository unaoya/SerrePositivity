module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
/-!
概要：貼り合わせた単体データの純粋な左右の成分を回収する。
方針：片側が空の矩形では純粋な成分の分岐を選び、端点の輸送を消す。
規約：HA 方程式を仮定しない。
使われ方：逆構成の元の図式と定値終点への制限の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

lemma dgCoherentBarJoinRawData_left_hom_heq {n m : ℕ}
    (s : SimplexData R C n) (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t)
    (K : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hK : 2 ≤ K.card) (ha : a = K.min' (Index.nonempty hK))
    (hb : b = K.max' (Index.nonempty hK)) (hk : k = 2 - (K.card : ℤ)) :
    HEq ((dgCoherentBarJoinRawData s t f).hom
      (dgCoherentBarJoinSubset K (∅ : Finset (Fin (m + 1))))
      (dgCoherentBarJoinLeft n m a) (dgCoherentBarJoinLeft n m b) k
      (by rw [dgCoherentBarJoinSubset_card]; simpa using hK)
      (by
        simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using
          Index.image_min (dgCoherentBarJoinLeft n m).monotone
            (ha.symm ▸ K.isLeast_min' _) _)
      (by
        simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using
          Index.image_max (dgCoherentBarJoinLeft n m).monotone
            (hb.symm ▸ K.isGreatest_max' _) _)
      (by rw [dgCoherentBarJoinSubset_card]; simpa using hk))
      (s.hom K a b k hK ha hb hk) := by
  dsimp only [dgCoherentBarJoinRawData]
  simp only [dgCoherentBarJoinLeftPart_subset, dgCoherentBarJoinRightPart_subset,
    dite_eq_left (Index.nonempty hK), dite_eq_right Finset.not_nonempty_empty]
  exact (gradedHomTransport_heq (A := R) (D := C) _ _ _ _).trans
    (SimplexData.hom_heq_of_indices_degree s
      (I := K) (J := K) rfl
      (by simpa only [dgCoherentBarJoinLeftPart_subset] using ha.symm)
      (by simpa only [dgCoherentBarJoinLeftPart_subset] using hb.symm) rfl)

lemma dgCoherentBarJoinRawData_right_hom_heq {n m : ℕ}
    (s : SimplexData R C n) (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t)
    (L : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (Index.nonempty hL))
    (hb : b = L.max' (Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ)) :
    HEq ((dgCoherentBarJoinRawData s t f).hom
      (dgCoherentBarJoinSubset (∅ : Finset (Fin (n + 1))) L)
      (dgCoherentBarJoinRight n m a) (dgCoherentBarJoinRight n m b) k
      (by rw [dgCoherentBarJoinSubset_card]; simpa using hL)
      (by
        simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using
          Index.image_min (dgCoherentBarJoinRight n m).monotone
            (ha.symm ▸ L.isLeast_min' _) _)
      (by
        simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using
          Index.image_max (dgCoherentBarJoinRight n m).monotone
            (hb.symm ▸ L.isGreatest_max' _) _)
      (by rw [dgCoherentBarJoinSubset_card]; simpa using hk))
      (t.hom L a b k hL ha hb hk) := by
  dsimp only [dgCoherentBarJoinRawData]
  simp only [dgCoherentBarJoinLeftPart_subset, dgCoherentBarJoinRightPart_subset,
    dite_eq_right Finset.not_nonempty_empty]
  exact (gradedHomTransport_heq (A := R) (D := C) _ _ _ _).trans
    (SimplexData.hom_heq_of_indices_degree t
      (I := L) (J := L) rfl
      (by simpa only [dgCoherentBarJoinRightPart_subset] using ha.symm)
      (by simpa only [dgCoherentBarJoinRightPart_subset] using hb.symm) rfl)

end SerrePositivity.InfinityCategories
