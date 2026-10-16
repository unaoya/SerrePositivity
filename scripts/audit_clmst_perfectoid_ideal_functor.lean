import SerrePositivity.CommutativeAlgebra.PerfectoidIdealFunctor
import SerrePositivity.CLMST.PerfectoidIdealTorComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.quotientPerfectoidizationMap
assert_no_sorry SerrePositivity.quotientPerfectoidizationMap_comp
assert_no_sorry SerrePositivity.quotientPerfectoidizationMap_mk
assert_no_sorry SerrePositivity.perfectoidIdeal_map_le
assert_no_sorry SerrePositivity.map_mem_perfectoidIdeal
assert_no_sorry SerrePositivity.perfectoidIdealQuotientMap
assert_no_sorry SerrePositivity.perfectoidIdealQuotientMap_mk
#print axioms SerrePositivity.quotientPerfectoidizationMap
#print axioms SerrePositivity.quotientPerfectoidizationMap_comp
#print axioms SerrePositivity.quotientPerfectoidizationMap_mk
#print axioms SerrePositivity.perfectoidIdeal_map_le
#print axioms SerrePositivity.map_mem_perfectoidIdeal
#print axioms SerrePositivity.perfectoidIdealQuotientMap
#print axioms SerrePositivity.perfectoidIdealQuotientMap_mk

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST CategoryTheory
attribute [local instance] HasDerivedCategory.standard

-- The E-side finite free comparison kills precisely the images of the original scalars.
theorem audit_original_ideal_scalars_in_extension_Tor
    (R E C : Type u) [CommRing R] [CommRing E] [CommRing C]
    [Algebra R E] [Algebra E C] [Algebra R C] [IsScalarTower R E C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hE : IsIntegralPerfectoid E p) (g : R)
    (r : ℕ) (f : C →ₗ[E] (Fin r → E))
    (hc : ∀ a ∈ perfectoidIdeal E p hE (algebraMap R E g),
      ∀ y : (Fin r → E) ⧸ f.range, a • y = 0)
    (hk : ∀ a ∈ perfectoidIdeal E p hE (algebraMap R E g),
      ∀ x : f.ker, a • x = 0)
    (N : ModuleCat.{u} E) (k : ℕ) (hN : ∀ x : N, (p : E) ^ k • x = 0)
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ perfectoidIdeal R p hR g) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  have h := perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison E p hE
    (algebraMap R E g) C r f hc hk N k hN i hi (algebraMap R E s)
    (map_mem_perfectoidIdeal p hR hE (algebraMap R E) g s hs)
  simpa only [IsScalarTower.algebraMap_apply R E C] using h

-- Arbitrary base maps, including maps to the zero ring, induce maps on the actual quotients.
theorem audit_original_kernel_quotient_map
    (R E : Type u) [CommRing R] [CommRing E]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hE : IsIntegralPerfectoid E p) (φ : R →+* E) (g : R) :
    ∃ f : R ⧸ perfectoidIdeal R p hR g →+* E ⧸ perfectoidIdeal E p hE (φ g),
      IsIntegralPerfectoid (E ⧸ perfectoidIdeal E p hE (φ g)) p ∧
      ∀ x : R, f (Ideal.Quotient.mk (perfectoidIdeal R p hR g) x) =
        Ideal.Quotient.mk (perfectoidIdeal E p hE (φ g)) (φ x) :=
  ⟨perfectoidIdealQuotientMap p hR hE φ g,
    perfectoidIdeal_quotient_isIntegralPerfectoid E p hE (φ g),
    perfectoidIdealQuotientMap_mk p hR hE φ g⟩

assert_no_sorry audit_original_ideal_scalars_in_extension_Tor
assert_no_sorry audit_original_kernel_quotient_map
#print axioms audit_original_ideal_scalars_in_extension_Tor
#print axioms audit_original_kernel_quotient_map
