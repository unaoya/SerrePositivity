module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeCFactor
public import SerrePositivity.InfinityCategories.Derived.Gluing.YonedaHomotopyIso

/-! 左零成分を持つ始域の実円錐について、標的と円錐の左成分を H⁰ で同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (hA : dgGluingFactorIsZero R C A.left)

def dgGluingConeObject_leftModuleIso_of_source_zero :
    (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R) (representable R B.left)) ≅
      (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingConeObject R C D M A B f hC hD).left)) := by
  let g := dgGluingConeLeftArrow R C D M A B f
  let T := moduleHomotopyConeTriangle R C g
  have hT := moduleHomotopyConeTriangle_distinguished R C g
  have hz : IsZero T.obj₁ := (dgGluingFactorIsZero_iff_representable R C A.left).1 hA
  have hi : IsIso T.mor₂ := (T.isZero₁_iff_isIso₂ hT).1 hz
  letI := hi
  exact asIso T.mor₂ ≪≫ dgGluingConeObject_leftIso R C D M A B f hC hD

def dgGluingConeObject_leftHomotopyIso_of_source_zero :
    (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) B.left) ≅
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R)
        (dgGluingConeObject R C D M A B f hC hD).left) :=
  dgGluingYonedaHomotopyPreimageIso R C _ _
    (dgGluingConeObject_leftModuleIso_of_source_zero R C D M A B f hC hD hA)

end SerrePositivity.InfinityCategories
