module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModulePropertyChoices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianCriterion

/-! # 三角的対象条件で制限した全 dg 加群の nerve の安定性

概要：K(D) の同型で閉じた三角的対象条件は、安定な充満 dg 加群部分圏を与える。
方針：実零頂点と全辺の双カルテジアンな選択を普遍性の反映から構成する。
規約：h の閉性は対象の閉性にのみ使う。使われ方：ホモトピー表現可能部分の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- K(D) の対象条件を満たす全 dg 加群の充満部分圏の nerve。 -/
abbrev dgModulePropertyNerve (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P))

variable (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 三角的対象条件の部分圏は実零頂点を含む。 -/
instance dgModulePropertyNerve_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (dgModulePropertyNerve A D P) where
  exists_zero := by
    let Z : DGFullSubcategory (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P) :=
      ⟨zeroModule A D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_zero A D P⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z, ?_, ?_⟩
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P)
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).1
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P)
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).2

/-- 三角的対象条件を満たす全 dg 加群の充満部分圏の nerve は安定。 -/
instance dgModulePropertyNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgModulePropertyNerve A D P) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProperty_bicartesian_fiber_exists A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProperty_bicartesian_cofiber_exists A D P)

/-- ホモトピー表現可能加群の replete な充満部分圏の nerve。 -/
abbrev dgHomotopyRepresentableNerve :=
  dgModulePropertyNerve A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D)

/-- dg 前三角性の下で、ホモトピー表現可能な全加群の部分圏の nerve は安定。 -/
instance dgHomotopyRepresentableNerve_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgHomotopyRepresentableNerve A D) :=
  dgModulePropertyNerve_isStable A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
