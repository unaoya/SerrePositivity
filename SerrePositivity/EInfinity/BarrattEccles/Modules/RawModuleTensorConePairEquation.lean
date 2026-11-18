module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeTailEquation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedClosed

/-!
概要：実 cone の全ての二点成分が HA 方程式を満たす。
方針：通常成分は元の面へ戻し、混合辺は同じ一点選択 cochain の閉性を使う。
規約：全次数の元の cone データを保持する。使われ方：残る正次混合成分の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hc : I.card = 2) :
    (strictRawModuleTensorConeData A X P Q c).Equation I := by
  by_cases h0 : (0 : Fin (n + 2)) ∈ I
  · intro a b k hI ha hb hk
    have ha0 : a = 0 := ha.trans
      ((I.isLeast_min' _).unique ⟨h0, fun _ _ => Fin.zero_le _⟩)
    have hk0 : k = 0 := by omega
    subst hk0
    have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
    have hcard : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card = 1 := by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega
    have hb' : b = ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' hJ).succ :=
      hb.trans (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst I hI h0).symm
    have hx : (strictRawModuleTensorConeData A X P Q c).obj a =
        ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P) := by
      change strictRawModuleTensorConeObj A X P Q c a = _
      rw [ha0, strictRawModuleTensorConeObj_zero]
    have hy : (strictRawModuleTensorConeData A X P Q c).obj b =
        ForgetEnrichment.to (Complex A)
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' hJ))) := by
      change strictRawModuleTensorConeObj A X P Q c b = _
      rw [hb', strictRawModuleTensorConeObj_succ]
    have he := strictRawModuleTensorConeData_hom_mixed A X P Q c I a b 0 hI ha hb hk ha0 h0
    simp only [Int.negOnePow_zero, one_smul] at he
    have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy rfl _ _ he
    have hz := strictRawModuleTensorElementSelectedCochainAtMax_closed A X P Q c
      (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) hJ hcard
    have he0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := 0 + 1) (l := 0 + 1) hx hy rfl
    have heq := eq_of_heq (hd.trans ((heq_of_eq hz).trans he0.symm))
    exact heq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ I a b 0 hI ha hb hk hc).symm
  · exact strictRawModuleTensorConeData_equation_without_zero A X P Q c I h0

end SerrePositivity.EInfinity.BarrattEccles
