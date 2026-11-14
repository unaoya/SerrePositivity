module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の A 側方程式

概要：A 側の微分式と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- Left 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).Equation (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb)
    (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]
        dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftA A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_first_heq A D f b hb _ _ _ _ _ _ _
  · unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]
    have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftBase A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftNative A D f b hb).1.val
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_apex A D f b hb) rfl
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb)
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftNative A D f b hb).1.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA_heq A D
        f b hb).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_diagonal_heq A D f b hb)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree_negOnePow,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero] using H
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftA_differential A D f b hb

/-- Right 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).Equation (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb)
    (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]
        dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_A A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget_right_eq A D f b) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftA A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_first_heq A D f b hb _ _ _ _ _ _ _
  · unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]
    have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightNative A D f b hb).1.val
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_A A D f b hb)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_apex A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget_right_eq A D f b)
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb)
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightNative A D f b hb).1.property
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA_heq_right A D f b hb).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_diagonal_heq A D f b hb)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree_negOnePow,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero] using H
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLiftA_differential A D f b hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
