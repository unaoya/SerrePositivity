module
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyScalarBaseChange
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyTorAnnihilator
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # Low local cohomology annihilation at the actual maximal support -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {R D C : Type u} [CommRing R] [CommRing D] [CommRing C]
variable [IsNoetherianRing R] [IsNoetherianRing D] [IsLocalRing D]
variable [Algebra R D] [Algebra D C] [Algebra R C] [IsScalarTower R D C]

/-- Parameter support and actual ring change transfer higher Tor annihilators
to low local cohomology at the maximal ideal, without regularity over D. -/
lemma parameterLocalCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (IsLocalRing.maximalIdeal D) i C c = 0 := by
  have hrad : ((Ideal.span (Set.range z)).map (algebraMap R D)).radical =
      (IsLocalRing.maximalIdeal D).radical := by
    rw [Ideal.map_span, ← Set.range_comp, hz.2,
      Ideal.IsPrime.radical (inferInstance : (IsLocalRing.maximalIdeal D).IsPrime)]
  apply (localCohomologyScalarEndomorphism_ring_change_eq_zero_iff
    (S := D) z (IsLocalRing.maximalIdeal D) hrad i c).mp
  exact localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    z hres C I hTor i hi c hc

/-- The original base ideal suffices; the established Tor image-ideal theorem
supplies the full coefficient-ring ideal used in the local cohomology argument. -/
lemma parameterLocalCohomologyScalarEndomorphism_eq_zero_of_baseIdeal_tor
    {S : Type u} [CommRing S] (ψ : S →+* C) (I : Ideal S)
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0)
    (i : ℕ) (hi : i < e) (s : S) (hs : s ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (IsLocalRing.maximalIdeal D) i C (ψ s) = 0 := by
  apply parameterLocalCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    z hz hres (I.map ψ) ?_ i hi (ψ s) (Ideal.mem_map_of_mem ψ hs)
  intro N j hj
  exact torCoefficientScalarEndomorphism_mapIdeal_eq_zero ψ I N j (hTor N j hj)

end SerrePositivity
