module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentedColumnTerminal
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeTailTerminal

/-!
概要：実二重 cone の末尾単体は、元の通常 augmentation の終端付き列の閉単体に等しい。
方針：全前面を同じ frame 単体へ戻し、全終端成分を同じ augmentation へ照合する。
規約：対象と全高次 cochain の厳密な一致。使われ方：大域 slice 評価と元の円柱の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeTail_eq_closed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail A X Y c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  have hf := (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail_front A X Y c).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_closed_front A X Y c).symm
  have ho : (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail A X Y c).obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)).obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).obj
        (_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom n (Fin.last (n + 1))) =
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c).obj (Fin.last (n + 1))
      rw [_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom_last, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last,
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_obj_last]
    | cast i => exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n => s.obj i) hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbl : b = Fin.last (n + 1)
  · exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail_hom_last A X Y c I a b k hI ha hb hk hbl).trans
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_hom_last A X Y c I a b k hI ha hb hk hbl).symm
  · have hf' := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData hf
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hf'
    exact _root_.SerrePositivity.ComplexLimits.complexSimplexData_hom_heq_of_front_eq A _ _ hf' I a b k hI ha hb hk hbl

end SerrePositivity.ComplexLimits
