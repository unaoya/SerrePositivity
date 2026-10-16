import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorMapZero
import Mathlib.Util.AssertNoSorry

-- KL-A2f: actual Milnor maps and zero composites under arbitrary tower maps.
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyShiftEquiv_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerProjection_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyIncoming_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyBoundary_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyProductMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyProductMap_apply
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyDifference_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimOneMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimitMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerMilnorInclusion_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerMilnorProjection_naturality
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerMilnorSequenceMap
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimitMap_eq_zero
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimOneMap_eq_zero
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap_homology_comp_eq_zero
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyShiftEquiv_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerProjection_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyIncoming_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyBoundary_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyProductMap
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyProductMap_apply
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyDifference_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyLimOneMap
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyLimitMap
#print axioms SerrePositivity.DerivedCompletion.complexTowerMilnorInclusion_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerMilnorProjection_naturality
#print axioms SerrePositivity.DerivedCompletion.complexTowerMilnorSequenceMap
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyLimitMap_eq_zero
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomologyLimOneMap_eq_zero
#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimitMap_homology_comp_eq_zero

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R]
  (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
  (g h : ∀ n, K n ⟶ K n)
  (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ t n)
  (hh : ∀ n, t n ≫ h n = h (n + 1) ≫ t n)

-- Distinct arbitrary endomorphisms; no assumption of base-ring scalar action.
example (i : ℤ) (hg₀ : ∀ n, HomologicalComplex.homologyMap (g n) i = 0)
    (hh₀ : ∀ n, HomologicalComplex.homologyMap (h n) (i - 1) = 0) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t t g hg) i ≫
      HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t t h hh) i = 0 :=
  complexTowerHomotopyLimitMap_homology_comp_eq_zero R t t g hg t h hh i hg₀ hh₀

-- The same map need not vanish on the whole complex to give a square-zero Hⁱ action.
example (i : ℤ) (hg₀ : ∀ n, HomologicalComplex.homologyMap (g n) i = 0)
    (hg₁ : ∀ n, HomologicalComplex.homologyMap (g n) (i - 1) = 0) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t t g hg) i ≫
      HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t t g hg) i = 0 :=
  complexTowerHomotopyLimitMap_homology_comp_eq_zero R t t g hg t g hg i hg₀ hg₁
