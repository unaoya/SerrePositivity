module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverFirst

/-!
概要：元の恒等錐を指定始点として、実二重 cone を終端 X 上の slice 内の cone 単体へ送る。
方針：最初の slice 頂点の厳密な同定と、点と標準単体の join 表示を使う。
規約：恒等錐の射影も元の X を回収する。使われ方：大域二重 join の自然写像。
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

def normalizedTensorIdentityOverPoint : (Δ[0] : SSet.{u + 1}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X) :=
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X))

lemma normalizedTensorIdentityOverPoint_projection :
    normalizedTensorIdentityOverPoint A X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (normalizedTensorConePoint A X) =
      normalizedTensorConePoint A X := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simpa only [normalizedTensorIdentityOverPoint, normalizedTensorConePoint,
    Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone_projection ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)

def normalizedTensorDoubleConeUnderOverSimplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (normalizedTensorIdentityOverPoint A X)) _⦋n⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X))).symm
      (normalizedTensorDoubleConeOverSimplex A X Y c), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inl_vertex]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X)).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (normalizedTensorDoubleConeOverSimplex A X Y c) = _
    simpa only [normalizedTensorIdentityOverPoint, Equiv.apply_symm_apply] using
      normalizedTensorDoubleConeOverSimplex_first_vertex A X Y c⟩

end SerrePositivity.EInfinity.ComplexLimits
