import SerrePositivity.BhattScholze.PerfectPrismResidueFactor
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_mk
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_symm_mk
assert_no_sorry SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_algebraMap
#print axioms SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv
#print axioms SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_mk
#print axioms SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_symm_mk
#print axioms SerrePositivity.BhattScholze.perfectPrismResidueFactorAlgEquiv_algebraMap

noncomputable section
universe u
open SerrePositivity SerrePositivity.BhattScholze
attribute [local instance] adicQuotientAlgebra

-- The inverse and coefficient diagram use each prism's own ideal and the original prism map.
theorem audit_actual_prism_factor_inverse_and_scalars
    (p : ℕ) [Fact p.Prime] (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S)
    (s : S) (x : R ⧸ PR.ideal) :
    letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
    let e := perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf
    e.symm (Ideal.Quotient.mk PS.ideal s) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) PR.ideal) s ∧
    e (algebraMap (R ⧸ PR.ideal) (S ⧸ Ideal.map (algebraMap R S) PR.ideal) x) =
      f.quotientMap x := by
  exact ⟨perfectPrismResidueFactorAlgEquiv_symm_mk PR PS hR hS f hf s,
    perfectPrismResidueFactorAlgEquiv_algebraMap PR PS hR hS f hf x⟩

assert_no_sorry audit_actual_prism_factor_inverse_and_scalars
#print axioms audit_actual_prism_factor_inverse_and_scalars
