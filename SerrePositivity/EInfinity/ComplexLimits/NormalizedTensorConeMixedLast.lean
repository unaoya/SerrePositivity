module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeComponents
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedTerminal
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_hom_mixed_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk)
      (k.negOnePow • (normalizedTensorElementUniversalLinear A X Y c).val.component
        (withoutFirst I) k (withoutFirst_nonempty hI h0)
        (by have := card_withoutFirst I h0; omega)) := by
  have hm : (withoutFirst I).max' (withoutFirst_nonempty hI h0) = Fin.last n := by
    apply Fin.succ_injective
    exact (max_withoutFirst I hI h0).trans (hb.symm.trans hbl)
  exact (normalizedTensorConeData_hom_mixed A X Y c I a b k hI ha hb hk ha0 h0).trans
    (normalizedTensorElementSelectedCochainAtMax_terminal_smul A X Y c
      (withoutFirst I) k (withoutFirst_nonempty hI h0)
      (by have := card_withoutFirst I h0; omega) hm k.negOnePow)

lemma normalizedTensorConeData_d_mixed_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq (differential A ((normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk))
      (k.negOnePow • (normalizedTensorElementUniversalLinear A X Y c).val.rhs
        (withoutFirst I) k (by have := card_withoutFirst I h0; omega)) := by
  have hx : (normalizedTensorConeData A X Y c).obj a = X := by
    change normalizedTensorConeObj A X Y c a = X
    rw [ha0, normalizedTensorConeObj_zero]
  have hy : (normalizedTensorConeData A X Y c).obj b =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)) := by
    change normalizedTensorConeObj A X Y c b = _
    rw [hbl]
    exact normalizedTensorConeObj_succ A X Y c (Fin.last n)
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy rfl _ _
    (normalizedTensorConeData_hom_mixed_last A X Y c I a b k hI ha hb hk ha0 hbl h0)
  exact hd.trans (heq_of_eq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul _ _).trans
    (congrArg (fun v => k.negOnePow • v)
      (normalizedTensorElementUniversalLinear_equation A X Y c (withoutFirst I) k
        (withoutFirst_nonempty hI h0) (by have := card_withoutFirst I h0; omega)))))

end SerrePositivity.EInfinity.ComplexLimits
