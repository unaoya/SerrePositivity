module
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveHomotopyComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarConeTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementDerivedComparison

/-! # U13 enhancementの実際の係数変更のshiftと三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectHomotopyInclusionIso (S : Set D) :
    scalarPerfectHomotopyExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onHomotopy ≅
      (perfectDGModuleInclusion A D S).onHomotopy ⋙ scalarModuleExtensionHomotopy φ D :=
  Quotient.natIsoLift _ (Functor.isoWhiskerRight (scalarPerfectClosedInclusionIso φ D S)
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)))

local instance (S : Set D) : (perfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ :=
  perfectDGModuleInclusionHomotopyCommShift A D S
local instance (S : Set (ScalarExtension.DGBaseChange φ D)) :
    (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D) S).onHomotopy.CommShift ℤ :=
  perfectDGModuleInclusionHomotopyCommShift A' (ScalarExtension.DGBaseChange φ D) S
local instance : (scalarModuleExtensionHomotopy φ D).CommShift ℤ :=
  scalarModuleExtensionHomotopyCommShift φ D

@[instance_reducible]
def scalarPerfectHomotopyExtensionCommShift (S : Set D) :
    (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  Functor.CommShift.ofComp (scalarPerfectHomotopyInclusionIso φ D S) ℤ

lemma scalarPerfectHomotopyInclusionIso_commShift (S : Set D) :
    letI := scalarPerfectHomotopyExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyInclusionIso φ D S).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (scalarPerfectHomotopyInclusionIso φ D S) ℤ

lemma scalarPerfectHomotopyExtensionIsTriangulated (S : Set D) :
    letI := scalarPerfectHomotopyExtensionCommShift φ D S
    (scalarPerfectHomotopyExtension φ D S).IsTriangulated := by
  let := scalarPerfectHomotopyExtensionCommShift φ D S
  let := scalarPerfectHomotopyInclusionIso_commShift φ D S
  let := perfectDGModuleInclusionHomotopyIsTriangulated A D S
  let := perfectDGModuleInclusionHomotopyIsTriangulated A'
    (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let := scalarModuleExtensionHomotopyIsTriangulated φ D
  exact (Functor.isTriangulated_iff_comp_right (scalarPerfectHomotopyInclusionIso φ D S)).2
    inferInstance

end SerrePositivity.DifferentialGraded
