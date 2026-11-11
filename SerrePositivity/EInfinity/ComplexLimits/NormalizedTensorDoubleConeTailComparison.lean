module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementAugmentedColumnTerminal
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeTailTerminal

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeTail_eq_closed {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    normalizedTensorDoubleConeTail A X Y c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementAugmentedColumn A X Y c ⋙ complexToClosed A) := by
  have hf := (normalizedTensorDoubleConeTail_front A X Y c).trans
    (normalizedTensorElementAugmentedColumn_closed_front A X Y c).symm
  have ho : (normalizedTensorDoubleConeTail A X Y c).obj =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
        (normalizedTensorElementAugmentedColumn A X Y c ⋙ complexToClosed A)).obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (normalizedTensorDoubleConeSimplex A X Y c).obj
        (doubleConeTailOrderHom n (Fin.last (n + 1))) =
        (normalizedTensorElementAugmentedColumn A X Y c).obj (Fin.last (n + 1))
      rw [doubleConeTailOrderHom_last, normalizedTensorDoubleConeSimplex_last,
        normalizedTensorElementAugmentedColumn_obj_last]
    | cast i => exact congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n => s.obj i) hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbl : b = Fin.last (n + 1)
  · exact (normalizedTensorDoubleConeTail_hom_last A X Y c I a b k hI ha hb hk hbl).trans
      (normalizedTensorElementAugmentedColumn_hom_last A X Y c I a b k hI ha hb hk hbl).symm
  · have hf' := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData hf
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hf'
    exact complexSimplexData_hom_heq_of_front_eq A _ _ hf' I a b k hI ha hb hk hbl

end SerrePositivity.EInfinity.ComplexLimits
