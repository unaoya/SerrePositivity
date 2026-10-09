module

public import SerrePositivity.IntersectionMultiplicity.LengthComparison
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.CharP.Algebra

/-! # Local algebra facts used to instantiate the first norm comparison -/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- A quotient-ring module is annihilated by the defining ideal. -/
lemma quotient_action_annihilator (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    I ≤ Module.annihilator R M := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r x]
  have hz : algebraMap R (R ⧸ I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hz, zero_smul]

/-- Passing to a module quotient only enlarges its annihilator. -/
lemma annihilator_le_quotient (M : Type u) [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Module.annihilator R M ≤ Module.annihilator R (M ⧸ N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  obtain ⟨x, rfl⟩ := N.mkQ_surjective x
  rw [← N.mkQ.map_smul, hr, map_zero]

/-- Residue surjectivity gives an actual isomorphism of residue fields. -/
noncomputable def residueFieldEquiv_of_surjective [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T]
    (hres : Function.Surjective ((residue T).comp (algebraMap R T))) :
    ResidueField R ≃+* ResidueField T := by
  let f := (residue T).comp (algebraMap R T)
  have : (RingHom.ker f).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f hres (K := ⊥)
  have hk : RingHom.ker f = maximalIdeal R := IsLocalRing.eq_maximalIdeal inferInstance
  exact (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hres)

/-- A finite local algebra has a power of its maximal ideal contained in the
extension of the base maximal ideal. -/
theorem maximalIdeal_pow_le_map_of_finite [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    ∃ n : ℕ, (maximalIdeal T) ^ n ≤ (maximalIdeal R).map (algebraMap R T) := by
  let I := (maximalIdeal R).map (algebraMap R T)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have : Module.Finite R (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  exact IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

end SerrePositivity
