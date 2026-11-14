module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeTerminalComposition
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimateCuts
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryDecomposition

/-!
概要：始点と終端を持つ実 cone の最後の切断合成を、同じ普遍成分へ同定する。
方針：二点右切断の次数を零へ戻し、元の混合成分との実合成を計算する。
規約：同じ切断と符号を保持する。使われ方：全 HA 右辺の線形座標への照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_cutCompose_penultimate_value {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst (I.filter (· ≤ penultimate I hI))) (k + 1)
        (withoutFirst_nonempty
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (a := a) (by rw [ha]; exact I.min'_mem _) (penultimate_mem I hI)
            (by rw [ha]; exact min_lt_penultimate I hI hc))
          (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩))
        (by have hsplit := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (penultimate_mem I hI)
            have hr := (right_card_two_iff_penultimate I hI _ (penultimate_mem I hI)
              (penultimate_lt_max I hI)).mpr rfl
            have hw := card_withoutFirst (I.filter (· ≤ penultimate I hI))
              (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩)
            have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hsplit
            have hwZ := congrArg (fun t : ℕ => (t : ℤ)) hw
            rw [hr] at hsZ
            push_cast at hsZ hwZ
            have harith : ∀ i l w t : ℤ, t = 2 - i → l + 2 = i + 1 →
                l = w + 1 → t + 1 = 1 - w := by intros; omega
            exact harith _ _ _ _ hk hsZ hwZ)) := by
  let s := strictRawModuleTensorConeData A X P Q c
  let j := penultimate I hI
  let L := I.filter (· ≤ j)
  let R := I.filter (j ≤ ·)
  have hj : j ∈ I := penultimate_mem I hI
  have haj : a < j := by rw [ha]; exact min_lt_penultimate I hI hc
  have hjb : j < b := by rw [hb]; exact penultimate_lt_max I hI
  have ham : IsLeast (I : Set (Fin (n + 2))) a := by rw [ha]; exact I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 2))) b := by rw [hb]; exact I.isGreatest_max' _
  have hL : 2 ≤ L.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ham.1 hj haj
  have hR : 2 ≤ R.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbm.1 hjb
  have hr : R.card = 2 :=
    (right_card_two_iff_penultimate I hI j hj (by rw [← hb]; exact hjb)).mpr rfl
  have hl : 2 - (L.card : ℤ) = k + 1 := by
    have hsplit : L.card + R.card = I.card + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hkR : (0 : ℤ) = 2 - (R.card : ℤ) := by omega
  have hsum : (2 - (L.card : ℤ)) + (2 - (R.card : ℤ)) = k + 1 := by omega
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s R j b _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s L a j _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl]
  have ht : HEq
      (s.hom R j b (2 - (R.card : ℤ)) hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl)
      (s.hom R j b 0 hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) hkR) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hkR.symm
  have hf : HEq
      (s.hom L a j (2 - (L.card : ℤ)) hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl)
      (s.hom L a j (k + 1) hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) hl.symm) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hl
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) rfl rfl rfl hl hkR.symm rfl
    _ _ _ _ ht hf hsum (add_zero (k + 1))
  exact hcomp.trans (strictRawModuleTensorConeData_terminal_compose_mixed A X P Q c L R a j b (k + 1)
    hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) hl.symm ha0
    (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩) hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) hkR hbl)

end SerrePositivity.EInfinity.BarrattEccles
