module
public import SerrePositivity.HomologicalAlgebra.DerivedAlgebraAssociativity
public import SerrePositivity.HomologicalAlgebra.DerivedSingleTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedSingleTensorUnit
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # Actual commutative algebra objects for discrete algebras and their derived tensor -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The existing actual derived multiplication and unit satisfy all monoid laws. -/
@[instance_reducible] def boundedAboveDerivedAlgebraMonObj
    (A : Type u) [CommRing A] [Algebra R A] :
    MonObj (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)) where
  one := boundedAboveDerivedAlgebraUnit (R := R) A
  mul := boundedAboveDerivedAlgebraMul (R := R) A
  one_mul := boundedAboveDerivedAlgebraUnit_mul A
  mul_one := boundedAboveDerivedAlgebraMul_unit A
  mul_assoc := boundedAboveDerivedAlgebraMul_assoc A

/-- The actual degree-zero derived object of an algebra is a commutative algebra object. -/
def boundedAboveDerivedAlgebra (A : Type u) [CommRing A] [Algebra R A] :
    CommMon (DerivedCategory.Minus (ModuleCat.{u} R)) := by
  letI := boundedAboveDerivedAlgebraMonObj (R := R) A
  letI : IsCommMonObj (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)) :=
    { mul_comm := boundedAboveDerivedAlgebraMul_comm A }
  exact ⟨boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)⟩

/-- The actual derived tensor of two algebras, with its canonical commutative product. -/
def boundedAboveDerivedTensorAlgebra
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    CommMon (DerivedCategory.Minus (ModuleCat.{u} R)) :=
  by
    let B := boundedAboveDerivedAlgebra (R := R) S
    let C := boundedAboveDerivedAlgebra (R := R) T
    letI := B.mon
    letI := B.comm
    letI := C.mon
    letI := C.comm
    exact ⟨B.X ⊗ C.X⟩

end SerrePositivity
