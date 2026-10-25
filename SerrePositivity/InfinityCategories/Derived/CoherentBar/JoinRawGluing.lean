module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedEndpoints
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
/-!
概要：左右の単体データと全混合成分を、一つの join 単体データへ貼り合わせる。
方針：任意の成分添字を左右へ分割し、空側の有無により成分を選ぶ。
規約：この構成自体は HA 方程式を仮定しない。
使われ方：高次逆比較の実単体データの構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

abbrev DGCoherentBarJoinMixedData {n m : ℕ} (s : SimplexData R C n)
    (t : SimplexData R C m) :=
  ∀ (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty) (k : ℤ),
    k = 2 - (K.card : ℤ) - (L.card : ℤ) →
    GradedHom R (s.obj (K.min' hK)) (t.obj (L.max' hL)) k

def dgCoherentBarJoinRawData {n m : ℕ} (s : SimplexData R C n)
    (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t) :
    SimplexData R C (n + m + 1) where
  obj := dgCoherentBarJoinObjects s.obj t.obj
  hom J a b k hJ ha hb hk := by
    classical
    let K := dgCoherentBarJoinLeftPart n m J
    let L := dgCoherentBarJoinRightPart n m J
    have hSet : dgCoherentBarJoinSubset K L = J := dgCoherentBarJoinSubset_parts n m J
    have hCard : K.card + L.card = J.card := dgCoherentBarJoinParts_card n m J
    by_cases hK : K.Nonempty
    · by_cases hL : L.Nonempty
      · have hA : a = dgCoherentBarJoinLeft n m (K.min' hK) := by
          rw [ha]
          simpa only [hSet] using
            dgCoherentBarJoinSubset_min K L hK (by simpa only [hSet] using Index.nonempty hJ)
        have hB : b = dgCoherentBarJoinRight n m (L.max' hL) := by
          rw [hb]
          simpa only [hSet] using
            dgCoherentBarJoinSubset_max K L hL (by simpa only [hSet] using Index.nonempty hJ)
        exact gradedHomTransport
          (show s.obj (K.min' hK) = dgCoherentBarJoinObjects s.obj t.obj a by
            rw [hA, dgCoherentBarJoinObjects_left])
          (show t.obj (L.max' hL) = dgCoherentBarJoinObjects s.obj t.obj b by
            rw [hB, dgCoherentBarJoinObjects_right]) rfl
          (f K L hK hL k (by rw [← hCard] at hk; push_cast at hk; omega))
      · have hLE : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
        have him : K.image (dgCoherentBarJoinLeft n m) = J := by
          simpa only [hLE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty]
            using hSet
        have hc : K.card = J.card := by simpa only [hLE, Finset.card_empty, add_zero] using hCard
        have hA : dgCoherentBarJoinLeft n m (K.min' hK) = a := by
          rw [ha]
          simpa only [him] using Index.image_min (dgCoherentBarJoinLeft n m).monotone
            (K.isLeast_min' hK) (hK.image (dgCoherentBarJoinLeft n m))
        have hB : dgCoherentBarJoinLeft n m (K.max' hK) = b := by
          rw [hb]
          simpa only [him] using Index.image_max (dgCoherentBarJoinLeft n m).monotone
            (K.isGreatest_max' hK) (hK.image (dgCoherentBarJoinLeft n m))
        exact gradedHomTransport
          (show s.obj (K.min' hK) = dgCoherentBarJoinObjects s.obj t.obj a by
            rw [← hA, dgCoherentBarJoinObjects_left])
          (show s.obj (K.max' hK) = dgCoherentBarJoinObjects s.obj t.obj b by
            rw [← hB, dgCoherentBarJoinObjects_left]) rfl
          (s.hom K (K.min' hK) (K.max' hK) k (by omega) rfl rfl (by rw [hc]; exact hk))
    · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
      have him : L.image (dgCoherentBarJoinRight n m) = J := by
        simpa only [hKE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union]
          using hSet
      have hc : L.card = J.card := by simpa only [hKE, Finset.card_empty, zero_add] using hCard
      have hL : L.Nonempty := Finset.card_pos.mp (by omega)
      have hA : dgCoherentBarJoinRight n m (L.min' hL) = a := by
        rw [ha]
        simpa only [him] using Index.image_min (dgCoherentBarJoinRight n m).monotone
          (L.isLeast_min' hL) (hL.image (dgCoherentBarJoinRight n m))
      have hB : dgCoherentBarJoinRight n m (L.max' hL) = b := by
        rw [hb]
        simpa only [him] using Index.image_max (dgCoherentBarJoinRight n m).monotone
          (L.isGreatest_max' hL) (hL.image (dgCoherentBarJoinRight n m))
      exact gradedHomTransport
        (show t.obj (L.min' hL) = dgCoherentBarJoinObjects s.obj t.obj a by
          rw [← hA, dgCoherentBarJoinObjects_right])
        (show t.obj (L.max' hL) = dgCoherentBarJoinObjects s.obj t.obj b by
          rw [← hB, dgCoherentBarJoinObjects_right]) rfl
        (t.hom L (L.min' hL) (L.max' hL) k (by omega) rfl rfl (by rw [hc]; exact hk))

end SerrePositivity.InfinityCategories
