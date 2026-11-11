module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentSliceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPointCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UniversalTransportReflection
/-!
概要：全 Hom の閉後合成の準同型性から、元の dg nerve の実 coslice 輸送の同値性を得る。
方針：同じ DK 後合成を coherent 輸送へ送り、充満忠実な同じ比較射と実辺の一致で戻す。
規約：前三角性も対象の小ささも不要。使われ方：R の代表加群からの実 augmentation の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 全 Hom の同じ閉後合成が準同型なら、その dg 実辺の coslice 輸送は全空間同値。 -/
lemma dgClosedCosliceTransport_isQCatEquivalence (x y z : D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (B := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D f)) := by
  let : Quasicategory (SimplicialNerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory R D)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (_root_.SerrePositivity.DifferentialGraded.ClosedCategory R D)
  have hC := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentCosliceTransport_isQCatEquivalence_of_sHom
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplicialPostcomp_isQCatEquivalence R D x y z f)
  have H := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceTransport_equivalence_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex R) x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful (R := R) (D := D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)).mp hC
  have hx := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetPoint R D x)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hx
  erw [hx] at H
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.edgeTransport_isQCatEquivalence_congr_edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentComparison_closed_edge R D _ _ f)).mp H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
