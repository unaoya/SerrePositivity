module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCoordinateCases
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
/-!
概要：join の HA 単体データは、純粋な左右の面と全混合成分により一意に決まる。
方針：成分添字を左右へ分割し、純粋な場合は既存の単射制限の成分比較を使う。
規約：方程式を課す前の単体データにも成立する。
使われ方：余錐空間の pinched Hom 比較の単射性と高次復元の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

private lemma hom_heq_of_image {l n : ℕ} (s t : SimplexData R C n)
    (α : Fin (l + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (h : s.pullback α = t.pullback α) (K : Finset (Fin (l + 1)))
    (J : Finset (Fin (n + 1))) (hImg : K.image α = J)
    (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) : HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk) := by
  have hcard : K.card = J.card :=
    (Finset.card_image_of_injective K hα).symm.trans (congrArg Finset.card hImg)
  have hK : 2 ≤ K.card := by omega
  have hA : α (K.min' (Index.nonempty hK)) = a := by
    rw [ha]
    simpa only [hImg] using Index.image_min α.monotone (K.isLeast_min' _)
      ((Index.nonempty hK).image α)
  have hB : α (K.max' (Index.nonempty hK)) = b := by
    rw [hb]
    simpa only [hImg] using Index.image_max α.monotone (K.isGreatest_max' _)
      ((Index.nonempty hK).image α)
  have hh := SimplexData.hom_heq_of_pullback_eq s t α α h K
    (K.min' (Index.nonempty hK)) (K.max' (Index.nonempty hK)) k hK rfl rfl
    (by rw [hcard]; exact hk) hα.injOn hα.injOn
  refine HEq.trans ?_ (hh.trans ?_)
  · exact SimplexData.hom_heq_of_indices_degree s hImg.symm hA.symm hB.symm rfl
  · exact SimplexData.hom_heq_of_indices_degree t hImg hA hB rfl

lemma dgCoherentBarJoinSimplexData_ext {n m : ℕ} (s t : SimplexData R C (n + m + 1))
    (hLeft : s.pullback (dgCoherentBarJoinLeft n m) =
      t.pullback (dgCoherentBarJoinLeft n m))
    (hRight : s.pullback (dgCoherentBarJoinRight n m) =
      t.pullback (dgCoherentBarJoinRight n m))
    (hMixed : ∀ (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))),
      K.Nonempty → L.Nonempty →
      ∀ (a b : Fin (n + m + 1 + 1)) (k : ℤ)
        (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
        (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
        (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
        (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)),
        HEq (s.hom (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
          (t.hom (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)) : s = t := by
  have hObj : s.obj = t.obj := by
    funext i
    refine dgCoherentBarJoin_cases (n := n) (m := m)
      (P := fun i => s.obj i = t.obj i) ?_ ?_ i
    · intro j
      exact congrArg (fun d : SimplexData R C n => d.obj j) hLeft
    · intro j
      exact congrArg (fun d : SimplexData R C m => d.obj j) hRight
  apply SimplexData.ext hObj
  apply HomFamily.heq_of_pointwise hObj
  intro J a b k hJ ha hb hk
  let K := dgCoherentBarJoinLeftPart n m J
  let L := dgCoherentBarJoinRightPart n m J
  have hSet : dgCoherentBarJoinSubset K L = J := dgCoherentBarJoinSubset_parts n m J
  by_cases hK : K.Nonempty
  · by_cases hL : L.Nonempty
    · have hJ' : 2 ≤ (dgCoherentBarJoinSubset K L).card := by simpa only [hSet] using hJ
      have ha' : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ') := by
        simpa only [hSet] using ha
      have hb' : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ') := by
        simpa only [hSet] using hb
      have hk' : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ) := by
        simpa only [hSet] using hk
      refine HEq.trans ?_ ((hMixed K L hK hL a b k hJ' ha' hb' hk').trans ?_)
      · exact SimplexData.hom_heq_of_indices_degree s hSet.symm rfl rfl rfl
      · exact SimplexData.hom_heq_of_indices_degree t hSet rfl rfl rfl
    · have hLE : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      have hImg : K.image (dgCoherentBarJoinLeft n m) = J := by
        simpa only [hLE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using hSet
      exact hom_heq_of_image s t (dgCoherentBarJoinLeft n m)
        (dgCoherentBarJoinLeft_injective n m) hLeft K J hImg a b k hJ ha hb hk
  · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hImg : L.image (dgCoherentBarJoinRight n m) = J := by
      simpa only [hKE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using hSet
    exact hom_heq_of_image s t (dgCoherentBarJoinRight n m)
      (dgCoherentBarJoinRight_injective n m) hRight L J hImg a b k hJ ha hb hk

end SerrePositivity.InfinityCategories
