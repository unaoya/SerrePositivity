module
public import SerrePositivity.InfinityCategories.Derived.DGModulePropertyChoices
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulated
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion

/-! # 三角的対象条件で制限した全 dg 加群の nerve の安定性

概要：K(D) の同型で閉じた三角的対象条件は、安定な充満 dg 加群部分圏を与える。
方針：実零頂点と全辺の双カルテジアンな選択を普遍性の反映から構成する。
規約：h の閉性は対象の閉性にのみ使う。使われ方：ホモトピー表現可能部分の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の対象条件を満たす全 dg 加群の充満部分圏の nerve。 -/
abbrev dgModulePropertyNerve (P : ObjectProperty (ModuleHomotopyCategory A D)) :=
  dgNerve A (DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P))

variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 三角的対象条件の部分圏は実零頂点を含む。 -/
instance dgModulePropertyNerve_hasZeroVertex : HasZeroVertex (dgModulePropertyNerve A D P) where
  exists_zero := by
    let Z : DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P) :=
      ⟨zeroModule A D, dgModuleHomotopyProperty_zero A D P⟩
    refine ⟨Simplex.vertex Z, ?_, ?_⟩
    · apply isInitialVertex_of_fullInclusion A (RightModule A D) (dgModuleHomotopyProperty A D P)
      rw [dgFunctorNerve_vertex]
      exact (dgModuleNerveZeroVertex_isZero A D).1
    · apply isTerminalVertex_of_fullInclusion A (RightModule A D) (dgModuleHomotopyProperty A D P)
      rw [dgFunctorNerve_vertex]
      exact (dgModuleNerveZeroVertex_isZero A D).2

/-- 三角的対象条件を満たす全 dg 加群の充満部分圏の nerve は安定。 -/
instance dgModulePropertyNerve_isStable : IsStable (dgModulePropertyNerve A D P) :=
  isStable_of_bicartesian_choices (dgModuleProperty_bicartesian_fiber_exists A D P)
    (dgModuleProperty_bicartesian_cofiber_exists A D P)

/-- ホモトピー表現可能加群の replete な充満部分圏の nerve。 -/
abbrev dgHomotopyRepresentableNerve :=
  dgModulePropertyNerve A D (dgRepresentableHomotopyProperty A D)

/-- dg 前三角性の下で、ホモトピー表現可能な全加群の部分圏の nerve は安定。 -/
instance dgHomotopyRepresentableNerve_isStable [IsDGPretriangulated A D] :
    IsStable (dgHomotopyRepresentableNerve A D) :=
  dgModulePropertyNerve_isStable A D (dgRepresentableHomotopyProperty A D)

end SerrePositivity.InfinityCategories
