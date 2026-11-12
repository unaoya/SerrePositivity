module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeOrdinaryComposition
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedComposition

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_terminal_compose_mixed {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (L R : Finset (Fin (n + 2))) (a j b : Fin (n + 2)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hj : j = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ))
    (ha0 : a = 0) (h0 : 0 ∈ L) (hR : 2 ≤ R.card)
    (hjR : j = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)) (hb : b = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : (0 : ℤ) = 2 - (R.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq (compose A ((normalizedTensorConeData A X Y c).hom R j b 0 hR hjR hb hkR)
      ((normalizedTensorConeData A X Y c).hom L a j k hL ha hj hk) (add_zero k))
      (k.negOnePow • (normalizedTensorElementUniversalLinear A X Y c).val.component
        (withoutFirst L) k (withoutFirst_nonempty hL h0)
        (by have := card_withoutFirst L h0; omega)) := by
  let J := withoutFirst L
  have hJ : J.Nonempty := withoutFirst_nonempty hL h0
  have hjm : j = (J.max' hJ).succ := hj.trans (max_withoutFirst L hL h0).symm
  have hj0 : j ≠ 0 := by rw [hjm]; exact Fin.succ_ne_zero _
  have hjb : j ≤ b := by rw [hbl]; exact Fin.le_last _
  have hf := normalizedTensorConeData_hom_mixed A X Y c L a j k hL ha hj hk ha0 h0
  have hg := normalizedTensorConeData_hom_ordinary_closed
    A X Y c R j b hR hjR hb hkR hj0 hjb
  have hg' : HEq ((normalizedTensorConeData A X Y c).hom R j b 0 hR hjR hb hkR)
      (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
        ((normalizedTensorElementDiagram A X Y).map
          (c.map (homOfLE (Fin.le_last (J.max' hJ))))))).val := by
    have ht : ∀ (i t i' t' : Fin (n + 1)) (hi : i = i') (ht : t = t')
        (hit : i ≤ t) (hit' : i' ≤ t'),
        HEq (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
          ((normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hit))))).val
          (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
            ((normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hit'))))).val := by
      intro i t i' t' hi ht hit hit'
      subst i'
      subst t'
      rfl
    exact hg.trans (ht _ _ _ _ (by rw [hjm, coneTailOrderHom_succ])
      (by rw [hbl]; exact coneTailOrderHom_succ (Fin.last n)) _ _)
  have hx : (normalizedTensorConeData A X Y c).obj a = X := by
    change normalizedTensorConeObj A X Y c a = X
    rw [ha0, normalizedTensorConeObj_zero]
  have hy : (normalizedTensorConeData A X Y c).obj j =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ)) := by
    change normalizedTensorConeObj A X Y c j = _
    rw [hjm, normalizedTensorConeObj_succ]
  have hz : (normalizedTensorConeData A X Y c).obj b =
      (normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)) := by
    change normalizedTensorConeObj A X Y c b = _
    rw [hbl]
    exact normalizedTensorConeObj_succ A X Y c (Fin.last n)
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hy hz rfl rfl rfl _ _ _ _ hg' hf
    (add_zero k) (add_zero k)
  exact hcomp.trans (heq_of_eq (normalizedTensorElementSelectedCochainAtMax_compose
    A X Y c J k hJ (by have := card_withoutFirst L h0; dsimp only [J]; omega) k.negOnePow))

end SerrePositivity.EInfinity.ComplexLimits
