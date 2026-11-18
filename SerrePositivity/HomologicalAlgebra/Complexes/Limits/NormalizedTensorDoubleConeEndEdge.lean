module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoubleConeEndEdgeIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSimplexComponentExt

/-!
概要：元の二重 cone の先端と終端を結ぶ実辺を、同じ恒等射の通常単体へ同定する。
方針：終端成分の実 augmentation を回収し、先端の恒等射を全一単体の等式へ戻す。
規約：対象と実辺全体の厳密な一致。使われ方：slice 内の最初の頂点の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSimplex_end_edge {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin 2)).obj X ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A (Complex A)
  · intro i
    fin_cases i
    · change _root_.SerrePositivity.ComplexLimits.complexRightConeObj A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c) X
        (0 : Fin (n + 2)).castSucc = X
      rw [_root_.SerrePositivity.ComplexLimits.complexRightConeObj_castSucc]
      rfl
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last A X Y c
  · intro I a b k hI ha hb hk
    have hU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.two_eq_univ I hI
    subst I
    have ha0 : a = 0 := ha.trans ((Finset.min'_eq_iff _ _ 0).2
      ⟨by simp, fun i _ => Fin.zero_le i⟩)
    have hb1 : b = 1 := hb.trans ((Finset.max'_eq_iff _ _ 1).2
      ⟨by simp, fun i _ => Fin.le_last i⟩)
    have hk0 : k = 0 := by simpa using hk
    subst ha0 hb1 hk0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom_injective n).injOn]
    change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X)) 0)
    have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom_injective n).injOn hI
    have he := _root_.SerrePositivity.ComplexLimits.complexRightConeData_hom_last A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplexAugmentation A X Y c)
      (Finset.univ.image (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n))
      (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n 0) (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n 1) 0 hII
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n).monotone
        (by rw [ha]; exact Finset.univ.isLeast_min' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n).monotone
        (by rw [hb]; exact Finset.univ.isGreatest_max' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII))
      (by rw [Finset.card_image_of_injective _ (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom_injective n)]; exact hk)
      (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom_one n)
    have hi0 : (Fin.last (n + 1)).predAboveOrderHom (_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom n 0) = 0 := by
      rw [_root_.SerrePositivity.ComplexLimits.doubleConeEndEdgeOrderHom_zero]
      change (Fin.last (n + 1)).predAbove ((0 : Fin (n + 2)).castSucc) = 0
      exact Fin.predAbove_last_castSucc
    have ht : ∀ i j : Fin (n + 2), i = j →
        HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c i)) 0)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
            (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c j)) 0) := by
      intro i j h
      subst j
      rfl
    have hv := ht _ _ hi0
    change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (𝟙 X)) 0) at hv
    exact he.trans hv
end SerrePositivity.ComplexLimits
