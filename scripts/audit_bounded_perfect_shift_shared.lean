import SerrePositivity.PerfectComplex.ClosedSupportRelations
import SerrePositivity.Asymptotic.RankQuotient
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
open scoped ZeroObject
universe v u
example {C : Type u} [Category.{v} C] [Preadditive C]
    {K : CochainComplex C ℤ} (hK : strictlyBoundedComplex C K) (n : ℤ) :
    strictlyBoundedComplex C (K⟦n⟧) := strictlyBoundedComplex_shift C hK n
example {R : Type u} [CommRing R] :
    strictlyPerfectComplex R (0 : CochainComplex (ModuleCat.{u} R) ℤ) :=
  strictlyPerfectComplex_zero
example {R : Type u} [CommRing R] {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (n : ℤ) : strictlyPerfectComplex R (P⟦n⟧) :=
  strictlyPerfectComplex_shift hp n

assert_no_sorry SerrePositivity.strictlyBoundedComplex_shift
assert_no_sorry SerrePositivity.strictlyPerfectComplex_zero
assert_no_sorry SerrePositivity.strictlyPerfectComplex_shift
#print axioms SerrePositivity.strictlyPerfectComplex_shift
