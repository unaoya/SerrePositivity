module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeEquations
/-!
概要：左右 pinched Hom の線形座標の反転に必要な削除符号を計算する。
方針：濃度 c に choose(c,2) の符号を付け、反転で交換する左右の点数を数える。
規約：既存の dg 反対模型を変更せず、その実有限集合の反転を使う。
使われ方：固定終点の標準 Hom 比較を既知の線形同値へ結ぶ。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar


def dgCoherentBarLinearReflectionSign (c : ℕ) : ℤˣ := (c.choose 2 : ℤ).negOnePow

lemma dgCoherentBarLinearReflectionSign_succ (c : ℕ) :
    dgCoherentBarLinearReflectionSign (c + 1) =
      (c : ℤ).negOnePow * dgCoherentBarLinearReflectionSign c := by
  unfold dgCoherentBarLinearReflectionSign
  rw [Nat.choose_succ_succ' c 1, Nat.choose_one_right, Nat.cast_add, Int.negOnePow_add]

lemma dgCoherentBarLinearReflectionSign_mul_self (c : ℕ) :
    dgCoherentBarLinearReflectionSign c * dgCoherentBarLinearReflectionSign c = 1 :=
  Int.units_mul_self _

lemma dgCoherentBarLinearReflection_card {n : ℕ} (J : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ J) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card + (J.filter (j < ·)).card + 1 = J.card := by
  have hRev := congrArg Finset.card (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_strictRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J) j.rev)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse, Fin.rev_rev] at hRev
  rw [hRev]
  have hPartition := Finset.card_filter_add_card_filter_not (s := J) (p := (· ≤ j))
  have hNot : J.filter (fun x => ¬ x ≤ j) = J.filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter, not_le]
  rw [hNot] at hPartition
  have hLe := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictLeft_card J j hj
  omega

lemma dgCoherentBarLinearReflection_delete_sign {n : ℕ} (J : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ J) :
    dgCoherentBarLinearReflectionSign J.card *
        ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card : ℤ) + 1).negOnePow =
      (((J.filter (j < ·)).card : ℤ) + 1).negOnePow *
        dgCoherentBarLinearReflectionSign (J.erase j).card := by
  have hErase := Finset.card_erase_add_one hj
  have hCard := dgCoherentBarLinearReflection_card J j hj
  have hE : ((J.erase j).card : ℤ) =
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card : ℤ) + ((J.filter (j < ·)).card : ℤ) := by
    omega
  have hSign : ((J.erase j).card : ℤ).negOnePow *
      ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card : ℤ) + 1).negOnePow =
        (((J.filter (j < ·)).card : ℤ) + 1).negOnePow := by
    rw [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).mpr
    refine ⟨(((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card : ℤ), ?_⟩
    omega
  rw [← hErase, dgCoherentBarLinearReflectionSign_succ]
  calc
    _ = (((J.erase j).card : ℤ).negOnePow *
          ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).filter (j.rev < ·)).card : ℤ) + 1).negOnePow) *
        dgCoherentBarLinearReflectionSign (J.erase j).card := by ac_rfl
    _ = _ := by rw [hSign]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
