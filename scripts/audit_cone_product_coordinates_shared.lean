import SerrePositivity.HomologicalAlgebra.CochainConeProduct
import SerrePositivity.HomologicalAlgebra.CochainLinearDualCone
import SerrePositivity.CommutativeAlgebra.GradedKoszul
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe u
variable {R : Type u} [CommRing R]
example (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    scalarConeXIsoProd a P q = mappingConeTermProdIso (smulId a P) q := rfl
example {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (q : ℤ) :
    mappingConeTermProdIso φ q =
      (DerivedCompletion.moduleConeDegreeEquiv φ q (q + 1) rfl).toModuleIso := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f => f.hom x) (mappingConeTermProdIso_fst φ q)
  · exact congrArg (fun f => f.hom x) (mappingConeTermProdIso_snd φ q)
assert_no_sorry SerrePositivity.mappingConeTermProdIso
assert_no_sorry SerrePositivity.mappingConeTermProdIso_fst
assert_no_sorry SerrePositivity.mappingConeTermProdIso_snd
assert_no_sorry SerrePositivity.mappingConeTermProdIso_d_fst
assert_no_sorry SerrePositivity.mappingConeTermProdIso_d_snd
assert_no_sorry SerrePositivity.cochainLinearDualConeIso
assert_no_sorry SerrePositivity.GradedKoszul.coneTermEquiv_d_fst
assert_no_sorry SerrePositivity.GradedKoszul.coneTermEquiv_d_snd
#print axioms SerrePositivity.cochainLinearDualConeIso
#print axioms SerrePositivity.GradedKoszul.coneTermEquiv_d_snd
