module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeOrdinaryComposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedComposition

/-!
概要：実 cone の混合成分と終端通常辺の合成を、同じ普遍 cochain 成分へ戻す。
方針：最大点の後続元の式で中間対象を合わせ、元の選択 cochain の合成式を使う。
規約：同じ次数・符号・端点を保つ。使われ方：最後の切断の実合成の評価。
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

lemma normalizedTensorConeData_terminal_compose_mixed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (L R : Finset (Fin (n + 2))) (a j b : Fin (n + 2)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hj : j = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ))
    (ha0 : a = 0) (h0 : 0 ∈ L) (hR : 2 ≤ R.card)
    (hjR : j = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)) (hb : b = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : (0 : ℤ) = 2 - (R.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq (compose A ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom R j b 0 hR hjR hb hkR)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom L a j k hL ha hj hk) (add_zero k))
      (k.negOnePow • (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst L) k (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hL h0)
        (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst L h0; omega)) := by
  let J := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst L
  have hJ : J.Nonempty := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hL h0
  have hjm : j = (J.max' hJ).succ := hj.trans (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst L hL h0).symm
  have hj0 : j ≠ 0 := by rw [hjm]; exact Fin.succ_ne_zero _
  have hjb : j ≤ b := by rw [hbl]; exact Fin.le_last _
  have hf := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y c L a j k hL ha hj hk ha0 h0
  have hg := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary_closed
    A X Y c R j b hR hjR hb hkR hj0 hjb
  have hg' : HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom R j b 0 hR hjR hb hkR)
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
          (c.map (homOfLE (Fin.le_last (J.max' hJ))))))).val := by
    have ht : ∀ (i t i' t' : Fin (n + 1)) (hi : i = i') (ht : t = t')
        (hit : i ≤ t) (hit' : i' ≤ t'),
        HEq (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hit))))).val
          (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
            ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hit'))))).val := by
      intro i t i' t' hi ht hit hit'
      subst i'
      subst t'
      rfl
    exact hg.trans (ht _ _ _ _ (by rw [hjm, _root_.SerrePositivity.ComplexLimits.coneTailOrderHom_succ])
      (by rw [hbl]; exact _root_.SerrePositivity.ComplexLimits.coneTailOrderHom_succ (Fin.last n)) _ _)
  have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a = X := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c a = X
    rw [ha0, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero]
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj j =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ)) := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c j = _
    rw [hjm, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ]
  have hz : (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj b =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)) := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c b = _
    rw [hbl]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ A X Y c (Fin.last n)
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hy hz rfl rfl rfl _ _ _ _ hg' hf
    (add_zero k) (add_zero k)
  exact hcomp.trans (heq_of_eq (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_compose
    A X Y c J k hJ (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst L h0; dsimp only [J]; omega) k.negOnePow))

end SerrePositivity.ComplexLimits
