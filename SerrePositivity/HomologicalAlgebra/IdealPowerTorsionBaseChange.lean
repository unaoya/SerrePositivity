module
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsionSupport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Independence of the coefficient ring for ideal-power torsion -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R D : Type u} [CommRing R] [CommRing D]

end SerrePositivity
