module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeMixedLast
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeFirstBoundary

/-!
概要：始点と終端を含む実 cone の内部削除成分を、同じ普遍 cochain の削除成分へ戻す。
方針：元の両端を保つ削除の式と、後続元の削除添字の一致を使う。
規約：同じ実成分・次数・符号を保つ。使われ方：混合 HA の全線形削除和の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_erased_succ_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (j : Fin (n + 1)) (hj : j.succ ∈ I) (hjb : j.succ < b)
    (hJ : ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase j).Nonempty)
    (hkJ : k + 1 = 1 - (((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase j).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.succ) a b (k + 1))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase j) (k + 1) hJ hkJ) := by
  let s := strictRawModuleTensorConeData A X P Q c
  have haj : a < j.succ := by rw [ha0]; exact Fin.succ_pos _
  have ham : IsLeast (I : Set (Fin (n + 2))) a := by rw [ha]; exact I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 2))) b := by rw [hb]; exact I.isGreatest_max' _
  have hE := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ham.1 hbm.1 haj hjb
  have haE := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min ham haj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  have hbE := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max hbm hjb (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  have hkE : k + 1 = 2 - ((I.erase j.succ).card : ℤ) := by
    have he := Finset.card_erase_add_one hj
    omega
  have h0E : (0 : Fin (n + 2)) ∈ I.erase j.succ :=
    Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero j).symm, h0⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hE haE hbE hkE]
  have h := strictRawModuleTensorConeData_hom_mixed_last A X P Q c (I.erase j.succ)
    a b (k + 1) hE haE hbE hkE ha0 hbl h0E
  have ht : ∀ (K K' : Finset (Fin (n + 1))) (he : K = K')
      (hK : K.Nonempty) (hK' : K'.Nonempty)
      (hd : k + 1 = 1 - (K.card : ℤ)) (hd' : k + 1 = 1 - (K'.card : ℤ)),
      (strictRawModuleTensorElementLinear A X P Q c).val.component K (k + 1) hK hd =
        (strictRawModuleTensorElementLinear A X P Q c).val.component K' (k + 1) hK' hd' := by
    intro K K' he hK hK' hd hd'
    subst K'
    rfl
  exact h.trans (heq_of_eq (congrArg (fun v => (k + 1).negOnePow • v)
    (ht _ _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_erase_succ I j) _ hJ _ hkJ)))

end SerrePositivity.EInfinity.BarrattEccles
