module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeMap
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeSimplex

/-!
概要：元の全次数の実 cone 単体は、退化を含む全作用素への自然性を持つ。
方針：同じ実データ全体の pullback の一致を単体の等式へ持ち上げる。
規約：元の対象・射・符号付き cochain を保持する。使われ方：大域 cone/prism の束ね。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (normalizedTensorConeSimplex A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      normalizedTensorConeSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact normalizedTensorConeData_pullback_map A X Y c θ

end SerrePositivity.EInfinity.ComplexLimits
