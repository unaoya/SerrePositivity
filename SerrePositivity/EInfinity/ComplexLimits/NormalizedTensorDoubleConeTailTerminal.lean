module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeTailFront

/-!
概要：実二重 cone の末尾単体の全終端成分は、同じ元の augmentation の閉 cochain である。
方針：後続延長の選択集合上の単射性と、元の実終端成分の回収を使う。
規約：高次零も同じ全次数の式で保持する。使われ方：通常終端付き列との全データ比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeTail_hom_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((normalizedTensorDoubleConeTail A X Y c).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map ((normalizedTensorElementAugmentation A X Y).app
        (c.obj ((Fin.last n).predAboveOrderHom a)))) k) := by
  let α := doubleConeTailOrderHom n
  have hLast : Fin.last (n + 1) ∈ I := by rw [← hbl, hb]; exact I.max'_mem _
  have hi : Set.InjOn α (I : Set (Fin (n + 2))) := by
    change Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom
      (Fin.succOrderEmb (n + 1)).toOrderHom) _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast I hLast]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.injOn_extend_withLast_iff _ _).mpr (Fin.succ_injective _).injOn
  have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (n + 2))) a by rw [ha]; exact I.isLeast_min' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hbI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (n + 2))) b by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hkI : k = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have hbl' : α b = Fin.last (n + 2) := by rw [hbl]; exact doubleConeTailOrderHom_last n
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  rw [normalizedTensorDoubleConeTail, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have he := complexRightConeData_hom_last A (normalizedTensorConeSimplexAugmentation A X Y c)
    (I.image α) (α a) (α b) k hII haI hbI hkI hbl'
  have ht : ∀ i j : Fin (n + 2), i = j →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
        (normalizedTensorConeAugmentationAt A X Y c i)) k)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
          (normalizedTensorConeAugmentationAt A X Y c j)) k) := by
    intro i j h
    subst j
    rfl
  have hv := ht _ _ (doubleConeTailOrderHom_predAbove n a han)
  change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
    ((normalizedTensorElementAugmentation A X Y).app
      (c.obj ((Fin.last n).predAboveOrderHom a)))) k) at hv
  exact he.trans hv

end SerrePositivity.EInfinity.ComplexLimits
