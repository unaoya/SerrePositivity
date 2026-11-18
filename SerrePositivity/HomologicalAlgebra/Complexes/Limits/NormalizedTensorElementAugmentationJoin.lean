module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentedColumnJoin
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveCoconePoint
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeUnderSimplex

/-!
概要：元の通常 augmentation の混合宇宙の全余錐を同じ複体 dg nerve へ送る。
方針：同じ余錐 join・同じ閉 nerve 包含・同じ元の自然変換円柱を保持する。
規約：終端・全列制限・全円柱の厳密な一致。使われ方：実 slice 評価の標準右脚との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementAugmentationJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[0] : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.coconeJoin (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationCocone A X Y) ≫
    nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

lemma normalizedTensorElementAugmentationJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[0] : SSet.{u + 1}) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin, ← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.coconeJoin_inr]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationCocone, _root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint,
    Equiv.apply_symm_apply]
  change (nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
  rfl

lemma normalizedTensorElementAugmentationJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin A X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)) := by
  have h := congrArg (fun f => f ≫ nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)) (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_join A X Y c)
  simp only [Category.assoc, SSet.yonedaEquiv_symm_comp] at h
  exact h.symm

lemma normalizedTensorElementAugmentationJoin_prism :
    (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin A X Y =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y)).h ≫
        nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) := by
  have h := congrArg (fun f => f ≫ nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.coconePrism_eq_homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationCocone A X Y))
  simpa only [Category.assoc, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationCocone] using h

end SerrePositivity.ComplexLimits
