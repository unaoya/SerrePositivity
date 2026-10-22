module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePrincipalUnit

/-!
概要：元の主切断の評価・単位合成と符号から、同じ中央相の全切断和を比較する。
方針：元の二つの切断・実評価成分・全添字と次数を保持する。
規約：全二次境界と混合 HA は別工程。使われ方：大域評価三角形の実三相単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTrianglePinched_cutCompose_principal {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (Index.nonempty hI)) = 2)
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k + 1 = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I
      (I.min' (Index.nonempty hI)) (I.max' (Index.nonempty hI)) k
        (ConeHeadIndex.second I hI))
      ((DGNerve.PinchedHom.toLinearSimplex
        ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
          (I.filter (fun i => τ i = 1)) (k + 1) hJ hkJ) := by
  let s := (normalizedTensorTrianglePinched A X Y c τ).toSimplexData
  let a := I.min' (Index.nonempty hI)
  let b := I.max' (Index.nonempty hI)
  let j := ConeHeadIndex.second I hI
  let L := I.filter (· ≤ j)
  let R := I.filter (j ≤ ·)
  have hj : j ∈ I := ConeHeadIndex.second_mem I hI
  have haj : a < j := ConeHeadIndex.min_lt_second I hI
  have hjb : j < b := ConeHeadIndex.second_lt_max I hI hc
  have ham : IsLeast (I : Set (Fin (n + 1))) a := I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 1))) b := I.isGreatest_max' _
  have hL : 2 ≤ L.card := Index.left_two ham.1 hj haj
  have hR : 2 ≤ R.card := Index.right_two hj hbm.1 hjb
  have hl : L.card = 2 :=
    (ConeHeadIndex.left_card_two_iff_second I hI j hj haj).mpr rfl
  have hr : 2 - (R.card : ℤ) = k + 1 := by
    have hsplit : L.card + R.card = I.card + 1 := Index.split_card hj
    omega
  have hkL : (0 : ℤ) = 2 - (L.card : ℤ) := by omega
  have hsum : (2 - (L.card : ℤ)) + (2 - (R.card : ℤ)) = k + 1 := by omega
  change HEq (s.cutCompose I a b k j) _
  unfold SimplexData.cutCompose
  rw [dite_eq_left hsum]
  rw [SimplexData.homOrZero_eq s R j b _ hR (Index.right_min hj _)
      (Index.right_max hbm hjb.le _) rfl,
    SimplexData.homOrZero_eq s L a j _ hL (Index.left_min ham haj.le _)
      (Index.left_max hj _) rfl]
  have ht : HEq
      (s.hom R j b (2 - (R.card : ℤ)) hR (Index.right_min hj _)
        (Index.right_max hbm hjb.le _) rfl)
      (s.hom R j b (k + 1) hR (Index.right_min hj _)
        (Index.right_max hbm hjb.le _) hr.symm) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hr
  have hf : HEq
      (s.hom L a j (2 - (L.card : ℤ)) hL (Index.left_min ham haj.le _)
        (Index.left_max hj _) rfl)
      (s.hom L a j 0 hL (Index.left_min ham haj.le _)
        (Index.left_max hj _) hkL) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hkL.symm
  have hcomp := gradedHom_compose_heq (A := A) rfl rfl rfl hkL.symm hr rfl
    _ _ _ _ ht hf hsum (zero_add (k + 1))
  exact hcomp.trans (normalizedTensorTrianglePinched_principal_composite A X Y c τ I hI
    hs1 hp1 haz hbt L R rfl (k + 1) hL (Index.left_min ham haj.le _)
    (Index.left_max hj _) hkL hR (Index.right_min hj _) (Index.right_max hbm hjb.le _)
    hr.symm hJ hkJ)

end SerrePositivity.EInfinity.ComplexLimits
