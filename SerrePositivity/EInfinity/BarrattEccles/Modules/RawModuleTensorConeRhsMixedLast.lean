module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeLinearBoundary
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeTerminalCut
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeRhsReduction

/-!
概要：始点と終端を含む実 cone の全 HA 右辺を、元の普遍線形右辺へ同定する。
方針：全内部削除和へ最後の実切断成分を足し、同じ全線形削除和を回収する。
規約：元の全有限和・符号・端点を保持する。使われ方：混合 HA 方程式の証明。
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

lemma strictRawModuleTensorConeData_rhs_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega)) := by
  let J := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I
  have hJ : 2 ≤ J.card := by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; dsimp only [J]; omega
  have hkJ : k = 1 - (J.card : ℤ) := by
    have hs := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0
    dsimp only [J]
    omega
  have hm : Fin.last n ∈ J := by
    have hbI : (Fin.last n).succ ∈ I := by
      change Fin.last (n + 1) ∈ I
      rw [← hbl, hb]
      exact I.max'_mem _
    simpa only [J, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst, Finset.mem_filter, Finset.mem_univ, true_and] using hbI
  let f (j : J) : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) (k + 1) :=
    (strictRawModuleTensorElementLinear A X P Q c).val.component (J.erase j.val) (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
      (by have := Finset.card_erase_add_one j.property; omega)
  have hx : (strictRawModuleTensorConeData A X P Q c).obj a = (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) := by
    change strictRawModuleTensorConeObj A X P Q c a = _
    rw [ha0, strictRawModuleTensorConeObj_zero]
  have hy : (strictRawModuleTensorConeData A X P Q c).obj b =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)) := by
    change strictRawModuleTensorConeObj A X P Q c b = _
    rw [hbl]
    exact strictRawModuleTensorConeObj_succ A X P Q c (Fin.last n)
  have hlin := strictRawModuleTensorConeData_linearBoundary_mixed_last
    A X P Q c I a b k hI ha hb hk ha0 hbl h0 hJ hkJ
  have hdeg : k + 1 = 1 - ((J.erase (Fin.last n)).card : ℤ) := by
    have he := Finset.card_erase_add_one hm
    omega
  have hcut := strictRawModuleTensorConeData_terminal_cut_component A X P Q c I a b k
    hI ha hb hk hc ha0 hbl h0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ hm) hdeg
  have hsum : (∑ j : J, if j.val < Fin.last n then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • ((k + 1).negOnePow • f j) else 0) +
      (k + 1).negOnePow • f ⟨Fin.last n, hm⟩ =
      k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs J k hkJ := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
    rw [dite_eq_left hJ]
    exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.sum_restore_terminal_linear J hm f k
  rw [strictRawModuleTensorConeData_rhs_reduced A X P Q c I a b k hI ha hb hk hc]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy rfl _ _ _ _ hlin hcut).trans (heq_of_eq hsum)

end SerrePositivity.EInfinity.BarrattEccles
