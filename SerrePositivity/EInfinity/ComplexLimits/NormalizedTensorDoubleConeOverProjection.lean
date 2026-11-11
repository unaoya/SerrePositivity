module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverJoin
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeJoin

/-!
概要：slice 内の元の大域二重 cone の射影は、元の大域 cone 自身と厳密に一致する。
方針：恒等錐の同じ先端への射影を保持し、全 coslice 単体の射影を uncurry する。
規約：点ごとの射の類ではなく大域写像の等式。使われ方：二重 join の元の前面。
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

lemma normalizedTensorDoubleConeOverJoin_projection :
    normalizedTensorDoubleConeOverJoin A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (normalizedTensorConePoint A X) = normalizedTensorConeJoin A X Y := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X)
  let q : S ⟶ C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (normalizedTensorConePoint A X)
  have ht : ∀ (p : (Δ[0] : SSet.{u + 1}) ⟶ S) (r : (Δ[0] : SSet.{u + 1}) ⟶ C),
      p ≫ q = r → ∀ (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r),
      (∀ (n : SimplexCategoryᵒᵖ) (c : K.obj n), (f.app n c).val ≫ q = (g.app n c).val) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry g := by
    intro p r hp f g hf
    subst r
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp]
    congr 1
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    exact hf n c
  apply ht (normalizedTensorIdentityOverPoint A X) (normalizedTensorConePoint A X)
    (normalizedTensorIdentityOverPoint_projection A X)
    (normalizedTensorDoubleConeUnderOverMap A X Y) (normalizedTensorConeUnderMap A X Y)
  rintro ⟨⟨n⟩⟩ c
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X))).symm
        (normalizedTensorDoubleConeOverSimplex A X Y c)) ≫ q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm (normalizedTensorConeSimplex A X Y c)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp,
    normalizedTensorDoubleConeOverSimplex_projection]

end SerrePositivity.EInfinity.ComplexLimits
