module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCommonRhs
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補データの共通面

概要：左右の Q・A を挿入した候補が A と後続部分からなる共通面で一致する。
方針：二つの挿入成分は共通解で比較し、残りは零未知基底の共通面へ戻す。
規約：HA Proposition 1.3.1.10。使われ方：左右の充填単体の貼合せ。
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

/-- 左右の候補は A と後続部分からなる共通面で一致する。 -/
lemma dgModuleConeBoundaryCandidate_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) := by
  have hi : Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective
  have hbase := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)
  have hobj : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)).obj =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate A D f b hb).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)).obj := by
    funext i
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro J x y k hJ hx hy hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases hq : J.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_suffix_heq_of_eq A D f b hb _ hq _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_suffix_heq_of_eq A D f b hb _ hq _ _ _ _ _ _ _).symm
  · by_cases ha : J.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) = insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
    · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_first_heq_of_eq A D f b hb _ ha _ _ _ _ _ _ _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_first_heq_of_eq A D f b hb _ ha _ _ _ _ _ _ _).symm
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftCandidate_hom_of_ne A D f b hb _ _ _ _ _ _ _ _ hq ha,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightCandidate_hom_of_ne A D f b hb _ _ _ _ _ _ _ _ hq ha]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) hbase J x y k hJ hx hy hk hi.injOn hi.injOn

end SerrePositivity.InfinityCategories.Project.DerivedCategories
