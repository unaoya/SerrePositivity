module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeOverSimplex

/-!
概要：終端 X 上の実二重 cone 単体の全自然性と、元の cone への厳密な射影を証明する。
方針：標準 join の自然性を同じ二重 cone の全自然性へ戻し、前面を回収する。
規約：同じ元の図式全体を保持する。使われ方：slice 内の大域 cone の組立。
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

lemma normalizedTensorDoubleConeOverSimplex_naturality {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X)).map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).op
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex A X Y c) := by
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (m + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)))
      (𝟙 Δ[0]) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  have hn := (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_pullback_map A X Y c θ).symm
  exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (m + 2) =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (m + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm s) hn

lemma normalizedTensorDoubleConeOverSimplex_projection {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X)).app (Opposite.op ⦋n + 1⦌)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverSimplex A X Y c) = _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n + 1] : SSet.{u + 1}) Δ[0] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
    ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_front A X Y c

end SerrePositivity.ComplexLimits
