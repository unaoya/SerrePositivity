module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Finite biproducts of module cochain complexes -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R]

instance (priority := 100) cochainComplexHasFiniteBiproducts :
    HasFiniteBiproducts (CochainComplex (ModuleCat.{u} R) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end SerrePositivity
