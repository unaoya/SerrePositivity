import SerrePositivity.PerfectComplex.HomotopyCategory
import SerrePositivity.Asymptotic.RankQuotient
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe v u
example {C : Type u} [Category.{v} C] [Preadditive C]
    (P : ObjectProperty (CochainComplex C ℤ)) (K : CochainComplex C ℤ) :
    P.strictMap (HomotopyCategory.quotient _ _) ((HomotopyCategory.quotient _ _).obj K) ↔ P K :=
  homotopyProperty_strictMap_quotient P K

assert_no_sorry SerrePositivity.homotopyProperty_strictMap_quotient
assert_no_sorry SerrePositivity.boundedHomotopyProperty_quotient
assert_no_sorry SerrePositivity.perfectHomotopyProperty_quotient
assert_no_sorry SerrePositivity.Asymptotic.rankSmallHomotopy_quotient
#print axioms SerrePositivity.homotopyProperty_strictMap_quotient
