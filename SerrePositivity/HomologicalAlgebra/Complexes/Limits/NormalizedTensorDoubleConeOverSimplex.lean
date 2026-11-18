module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeUnderSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：元の二重 cone 単体を、同じ終端 X 上の slice の実単体へ送る。
方針：標準単体と点の join を同じ二重 cone で写し、最後の頂点を厳密に固定する。
規約：同じ元の単体全体を使う。使われ方：大域二重 cone の slice 内での組立。
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

lemma normalizedTensorDoubleConeSimplex_last_vertex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ (Fin.last (n + 2))).op
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last A X Y c

def normalizedTensorDoubleConeOverSimplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X)) _⦋n + 1⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ (Fin.last (n + 2))).op
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c) = _
    simpa only [_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last_vertex A X Y c⟩

end SerrePositivity.ComplexLimits
