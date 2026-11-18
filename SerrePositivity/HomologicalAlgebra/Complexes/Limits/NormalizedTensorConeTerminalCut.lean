module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConePenultimateValue
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeFirstBoundary

/-!
概要：実 cone の最後の切断を、元の普遍 cochain の終端削除成分へ同定する。
方針：最後の切断の実評価と、始点回収後の左集合の厳密な一致を使う。
規約：同じ切断・符号・次数を保つ。使われ方：混合 HA の全線形右辺の復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_terminal_cut_component {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I)
    (hJ : ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n)).Nonempty)
    (hkJ : k + 1 = 1 - (((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).cutCompose I a b k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI))
      ((k + 1).negOnePow • (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component
        ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n)) (k + 1) hJ hkJ) := by
  have h := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_cutCompose_penultimate_value A X Y c I a b k
    hI ha hb hk hc ha0 hbl h0
  have ht : ∀ (K K' : Finset (Fin (n + 1))) (he : K = K')
      (hK : K.Nonempty) (hK' : K'.Nonempty)
      (hd : k + 1 = 1 - (K.card : ℤ)) (hd' : k + 1 = 1 - (K'.card : ℤ)),
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component K (k + 1) hK hd =
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component K' (k + 1) hK' hd' := by
    intro K K' he hK hK' hd hd'
    subst K'
    rfl
  exact h.trans (heq_of_eq (congrArg (fun v => (k + 1).negOnePow • v)
    (ht _ _ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_left_penultimate_last I hI (hb.symm.trans hbl)) _ hJ _ hkJ)))

end SerrePositivity.ComplexLimits
