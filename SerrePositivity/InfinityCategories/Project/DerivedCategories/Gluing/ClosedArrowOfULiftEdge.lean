module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedArrowOfEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-! 持ち上げた dg nerve の実辺も、元の同じ閉射の持ち上げへ厳密に戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgGluingClosedArrowOfULiftEdge (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    (x y : D) (b : ((SSet.uliftFunctor.{w, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).Edge
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) :
    ∃ a : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y,
      Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max u v, w}
        (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D a)) = b := by
  let c : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) :=
    ⟨b.edge.down, congrArg ULift.down b.src_eq, congrArg ULift.down b.tgt_eq⟩
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedArrowOfEdge R D x y c
  refine ⟨a, ?_⟩
  apply Edge.ext
  apply ULift.ext
  exact congrArg Edge.edge ha

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
