import SerrePositivity.PerfectComplex.Eigen.Cubic
import SerrePositivity.CategoryTheory.Abelian.ShortComplex
import SerrePositivity.CategoryTheory.Triangulated.Idempotent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CochainCubicAction.comapIso
 SerrePositivity.CochainCubicAction.comapIso_hom
 SerrePositivity.shortExactCokernelIso_π_hom
 SerrePositivity.three_components_rotation

open CategoryTheory SerrePositivity
universe u
example {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (τ : CochainCubicAction L) :
    (CochainCubicAction.comapIso e τ).map = e.hom ≫ τ.map ≫ e.inv := rfl
#print axioms SerrePositivity.CochainCubicAction.comapIso
#print axioms SerrePositivity.shortExactCokernelIso_π_hom
