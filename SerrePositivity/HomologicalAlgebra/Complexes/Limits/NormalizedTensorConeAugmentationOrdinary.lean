module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeAugmentation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeOrdinaryComposition

/-!
概要：元の cone の通常辺と同じ終端 augmentation の実合成は、始点 augmentation である。
方針：同じ閉 frame 辺を回収し、元の自然変換の自然性と閉 cochain の合成式を使う。
規約：元の実辺と全端点を保つ。使われ方：二重 cone の通常三点方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeAugmentationAt_compose_ordinary_pair {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b))).val
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c a))).val := by
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hb0 : b ≠ 0 := ne_of_gt ((Fin.zero_le a).trans_lt hab)
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr ha0
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hb0
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp hab.le
  let f := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hij))
  let g := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj j)
  let h := (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i)
  have hnat : f ≫ g = h := by
    exact ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).naturality
      (c.map (homOfLE hij))).trans (Category.comp_id _)
  have hg := _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_ordinary_closed A X Y c I i.succ j.succ
    hI ha hb hk (Fin.succ_ne_zero _) hab.le
  change HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I i.succ j.succ 0 hI ha hb hk)
    (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)).val at hg
  change compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map g)).val
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I i.succ j.succ 0 hI ha hb hk) (add_zero 0) =
    (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map h)).val
  rw [eq_of_heq hg]
  have hfg : (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f ≫ (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map g =
      (_root_.SerrePositivity.ComplexLimits.complexToClosed A).map h :=
    ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map_comp f g).symm.trans (congrArg ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map) hnat)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp
    ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map g)).symm.trans
    (congrArg (fun q : (_root_.SerrePositivity.ComplexLimits.complexToClosed A).obj ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj
      (c.obj i)) ⟶ (_root_.SerrePositivity.ComplexLimits.complexToClosed A).obj X => (closedHomEquiv A (Complex A) _ _ q).val) hfg)

end SerrePositivity.ComplexLimits
