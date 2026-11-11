module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DecompositionFactors
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeLeftProjectionIso

/-! D 余単位の同じ実円錐を、元の左射影の C 切断と H⁰ で同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionCFactor R C D M hC hD X

def dgGluingDecompositionLeftHomotopyIso :
    (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) X.left) ≅
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) (W).val.left) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject_leftHomotopyIso_of_source_zero R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource R C D M hC X) X
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionArrow R C D M hC X) hC hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDecompositionDSource_left_zero R C D M hC X)

/-- 因子同値の同じ逆関手と単位で、実円錐を左射影の C 切断へ同定。 -/
def dgGluingDecompositionCSectionIso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionHomotopy R C D M hD).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onHomotopy.obj
        ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X))) ≅
      (toHomotopy R G).obj (ForgetEnrichment.of (Complex R) (W).val) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorHomotopyEquivalence R C D M hD
  let a := (toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M)).obj (ForgetEnrichment.of (Complex R) W)
  let h := e.inverse.mapIso (dgGluingDecompositionLeftHomotopyIso R C D M hC hD X)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorInclusion R C D M).onHomotopy.mapIso
    (h ≪≫ (e.unitIso.app a).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
