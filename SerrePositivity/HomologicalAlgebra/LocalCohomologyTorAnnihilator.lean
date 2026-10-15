module
public import SerrePositivity.HomologicalAlgebra.KoszulDualTorComparison
public import SerrePositivity.HomologicalAlgebra.KoszulLocalCohomologyAction

/-! # Higher Tor annihilators act by zero on low local cohomology -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Higher Tor zero actions transfer through the actual dual Koszul system to local cohomology. -/
lemma localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    [IsNoetherian R R] {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (Ideal.span (Set.range z)) i C c = 0 := by
  apply localCohomologyScalarEndomorphism_eq_zero_of_dualKoszul_stages z i C hres c
  intro n
  exact koszulDualHomology_coefficient_scalar_eq_zero_of_tor_annihilated
    (fun j => z j ^ n) (hres n) C I hTor i hi c hc

/-- Regular standard parameters supply all power resolutions for arbitrary coefficients. -/
lemma regularLocalCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    [IsLocalRing R] [IsNoetherianRing R] {e : ℕ} (z : Fin e → R)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z))
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (IsLocalRing.maximalIdeal R) i C c = 0 := by
  rw [← hz]
  exact localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated z
    (isKoszulResolution_all_powers z hz hreg) C I hTor i hi c hc

end SerrePositivity
