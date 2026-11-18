module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedTerminal
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual

/-!
概要：始点と終端を含む実 cone 成分と微分を、同じ普遍単体の線形座標へ同定する。
方針：終端尾が恒等であることと、元の符号付き成分・線形微分方程式を使う。
規約：元の符号・同じ有限集合・端点輸送を保持する。
使われ方：混合 HA 方程式の左辺と削除成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0)
        (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega)) := by
  have hm : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0) = Fin.last n := by
    apply Fin.succ_injective
    exact (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst I hI h0).trans (hb.symm.trans hbl)
  exact (strictRawModuleTensorConeData_hom_mixed A X P Q c I a b k hI ha hb hk ha0 h0).trans
    (strictRawModuleTensorElementSelectedCochainAtMax_terminal_smul A X P Q c
      (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0)
      (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega) hm k.negOnePow)

lemma strictRawModuleTensorConeData_d_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq (differential A ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk))
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega)) := by
  have hx : (strictRawModuleTensorConeData A X P Q c).obj a = (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) := by
    change strictRawModuleTensorConeObj A X P Q c a = _
    rw [ha0, strictRawModuleTensorConeObj_zero]
  have hy : (strictRawModuleTensorConeData A X P Q c).obj b =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)) := by
    change strictRawModuleTensorConeObj A X P Q c b = _
    rw [hbl]
    exact strictRawModuleTensorConeObj_succ A X P Q c (Fin.last n)
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy rfl _ _
    (strictRawModuleTensorConeData_hom_mixed_last A X P Q c I a b k hI ha hb hk ha0 hbl h0)
  exact hd.trans (heq_of_eq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul _ _).trans
    (congrArg (fun v => k.negOnePow • v)
      (strictRawModuleTensorElementLinear_equation A X P Q c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0) (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega)))))

end SerrePositivity.EInfinity.BarrattEccles
