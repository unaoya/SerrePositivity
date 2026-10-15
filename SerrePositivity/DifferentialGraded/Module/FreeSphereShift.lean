module
public import SerrePositivity.DifferentialGraded.Module.TensorShift
public import SerrePositivity.DifferentialGraded.Module.Cells
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # 自由sphereの整数shift -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- コチェイン規約：sphere nのshift sはsphere (n-s)。 -/
def complexSphereShiftIso (n s : ℤ) : (complexSphere A n)⟦s⟧ ≅ complexSphere A (n - s) :=
  ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso s (n - s) n (by omega)).app
    (𝟙_ (ModuleCat A))

/-- 自由sphereのshiftを主dg加群圏で同定する。 -/
def freeSphereShiftIso (x : D) (n s : ℤ) :
    (freeSphere A D x n)⟦s⟧ ≅ freeSphere A D x (n - s) :=
  (freeAtShiftIso A D x (complexSphere A n) s).symm ≪≫
    (freeAt x).mapIso (complexSphereShiftIso A n s)

end SerrePositivity.DifferentialGraded
