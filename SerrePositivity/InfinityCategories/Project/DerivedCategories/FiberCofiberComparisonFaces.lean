module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexTrianglePostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberCofiberDescEquivalence

/-! # 双対比較の後合成三角形

概要：cofiber 三角形を明示的比較で後合成すると、元の標準 fiber 三角形になる。
方針：二脚・対角・ホモトピーの厳密な保存を二単体の外延性へ渡す。
規約：実際の二単体の等式。使われ方：D7 の比較三単体の終点面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 下側の標準 cofiber 三角形の後合成は元の fiber 下三角形。 -/
lemma fiberCofiberLower_postcompose (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeComplexTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
      (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomotopy_differential _ _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · rfl
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_inclusionB g h)
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_diagonal g h)
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_homotopy g h)

/-- 上側の標準 cofiber 三角形の後合成は元の fiber 上三角形。 -/
lemma fiberCofiberUpper_postcompose (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeComplexTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) 0
      (by simp only [δ_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal, sub_self]) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i; fin_cases i <;> rfl
  · rfl
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_inclusionC g h)
  · apply heq_of_eq
    exact congrArg Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_diagonal g h)
  · exact heq_of_eq (Cochain.zero_comp _ (add_zero (-1)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
