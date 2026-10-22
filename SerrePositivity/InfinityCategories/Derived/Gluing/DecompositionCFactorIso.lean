module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DecompositionFactors
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeLeftProjectionIso

/-! D 余単位の同じ実円錐を、元の左射影の C 切断と H⁰ で同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (X : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M
local notation "W" => dgGluingDecompositionCFactor R C D M hC hD X

def dgGluingDecompositionLeftHomotopyIso :
    (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) X.left) ≅
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) (W).val.left) :=
  dgGluingConeObject_leftHomotopyIso_of_source_zero R C D M
    (dgGluingDecompositionDSource R C D M hC X) X
    (dgGluingDecompositionArrow R C D M hC X) hC hD
    (dgGluingDecompositionDSource_left_zero R C D M hC X)

/-- 因子同値の同じ逆関手と単位で、実円錐を左射影の C 切断へ同定。 -/
def dgGluingDecompositionCSectionIso :
    (dgGluingCSectionHomotopy R C D M hD).obj
      ((dgGluingLeft R C D M).onHomotopy.obj
        ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X))) ≅
      (toHomotopy R G).obj (ForgetEnrichment.of (Complex R) (W).val) := by
  let e := dgGluingCFactorHomotopyEquivalence R C D M hD
  let a := (toHomotopy R (DGGluingCFactor R C D M)).obj (ForgetEnrichment.of (Complex R) W)
  let h := e.inverse.mapIso (dgGluingDecompositionLeftHomotopyIso R C D M hC hD X)
  exact (dgGluingCFactorInclusion R C D M).onHomotopy.mapIso
    (h ≪≫ (e.unitIso.app a).symm)

end SerrePositivity.InfinityCategories
