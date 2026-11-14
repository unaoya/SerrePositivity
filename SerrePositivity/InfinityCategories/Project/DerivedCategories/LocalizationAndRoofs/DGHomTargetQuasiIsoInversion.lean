module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomTargetTransportRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleUnderlyingCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedCosliceTransport
public import SerrePositivity.DifferentialGraded.Derived.Projective
/-!
概要：全 Hom 後合成の準同型性を同じ空間値 Hom 関手の実辺の可逆性へ昇格する。
方針：同じ実 coslice 輸送と pointed 全空間の比較を使う。
規約：生の終点の射影性は不要。使われ方：一般 tensor–Hom の ∞ 随伴への準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ全 Hom 関手と実辺による比較。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_invertsPostcomposition
    (x y z : C)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R C (x := x) f)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((SSet.Edge.ofTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f))).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  let e := SSet.Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCosliceTransport_isQCatEquivalence R C x y z f
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgEdgeTransport_ulift_isQCatEquivalence.{max (u + 1) v,
    max (u + 1) v + 1} p e he
  have ht := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftFibrationSquareTransport_isQCatEquivalence_iff
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map p) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay R C x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_projection R C x)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v,
      max (u + 1) v + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z))).mp hu
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence _ ht
/-- 同じ全 Hom 関手と実辺による比較。 -/
lemma dgModuleHomTargetUnderlyingSpaceInfinity_invertsQuasiIso
    (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (T : _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (hT : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) T))
    {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((SSet.Edge.ofTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R D) f))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (RightModule R D) T)) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R (RightModule R D) (x := T) f) :=
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_postcompose_quasiIso R D hT f hf
  exact dgHomTargetUnderlyingSpaceInfinity_invertsPostcomposition R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) T M N f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
