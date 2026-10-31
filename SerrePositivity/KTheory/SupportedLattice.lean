module
public import SerrePositivity.KTheory.TorsionAnnihilator
public import SerrePositivity.CommutativeAlgebra.Localization.Lattice
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # Finite supported lattices in localized modules -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
universe u
namespace SerrePositivity
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (P : Submonoid R) [IsLocalization P B]
  {N : Type u} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- The inverse-image support condition supplies an annihilating power of the defining ideal. -/
lemma exists_pow_annihilator_of_localized_support [IsNoetherianRing R]
    [Module.Finite B N] (J : Ideal R)
    (h : Module.support B N ⊆ supportPullback (algebraMap R B) (supportZeroLocus J)) :
    ∃ n : ℕ, ∀ r ∈ J ^ n, ∀ x : N, r • x = 0 := by
  have hs : Module.support B N ⊆ PrimeSpectrum.zeroLocus (J.map (algebraMap R B)) := by
    rw [supportPullback_zeroLocus] at h
    exact h
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hs
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hs
    (J.fg_of_isNoetherianRing.map (algebraMap R B))
  refine ⟨n, fun r hr x => ?_⟩
  have hm : algebraMap R B r ∈ (J.map (algebraMap R B)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have he := Module.mem_annihilator.mp (hn hm) x
  simpa only [algebraMap_smul] using he

/-- Every finite submodule inherits the original closed support. -/
lemma finite_lattice_supportedOn [IsNoetherianRing R] [Module.Finite B N]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hN : Module.support B N ⊆ supportPullback (algebraMap R B) Z)
    (L : Submodule R N) (hL : L.FG) :
    finiteModuleSupportedOn Z (ModuleCat.of R L) := by
  have : Module.Finite R L := Module.Finite.of_fg hL
  refine ⟨inferInstance, ?_⟩
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp Z.isClosed
  have hZ : Z = supportZeroLocus J := by
    apply TopologicalSpace.Closeds.ext
    exact hJ
  obtain ⟨n, hn⟩ := exists_pow_annihilator_of_localized_support (B := B) J (hZ ▸ hN)
  intro p hp
  rw [hZ]
  change J ≤ p.asIdeal
  intro r hr
  have ha : r ^ n ∈ Module.annihilator R L := by
    rw [Module.mem_annihilator]
    intro x
    apply Subtype.ext
    exact hn (r ^ n) (Ideal.pow_mem_pow hr n) x
  exact p.isPrime.mem_of_pow_mem n
    ((Module.mem_support_iff_of_finite.mp hp) ha)

/-- A supported finite localized module has a finite supported lattice. -/
lemma exists_supported_lattice [IsNoetherianRing R] [Module.Finite B N]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hN : Module.support B N ⊆ supportPullback (algebraMap R B) Z) :
    ∃ L : Submodule R N, L.FG ∧ IsLocalizationLattice P L ∧
      finiteModuleSupportedOn Z (ModuleCat.of R L) := by
  obtain ⟨L, hL, hloc⟩ := exists_finite_lattice (B := B) P (N := N)
  exact ⟨L, hL, hloc, finite_lattice_supportedOn (B := B) Z hN L hL⟩


/-- Bundle the finite generation, support, and denominator-clearing data of a lattice. -/
structure SupportedLocalizationLattice (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (N : Type u) [AddCommGroup N] [Module R N] where
  carrier : Submodule R N
  fg : carrier.FG
  support : Module.support R carrier ⊆ Z
  denominators : IsLocalizationLattice P carrier

namespace SupportedLocalizationLattice
variable {P} {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
instance (L : SupportedLocalizationLattice P Z N) : Module.Finite R L.carrier :=
  Module.Finite.of_fg L.fg

/-- The supported finite module represented by a lattice. -/
abbrev obj (L : SupportedLocalizationLattice P Z N) : SupportedFGModuleOn Z :=
  ⟨ModuleCat.of R L.carrier, inferInstance, L.support⟩
end SupportedLocalizationLattice

/-- Bundled existence for later construction of the inverse on Grothendieck groups. -/
lemma nonempty_supportedLocalizationLattice [IsNoetherianRing R] [Module.Finite B N]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hN : Module.support B N ⊆ supportPullback (algebraMap R B) Z) :
    Nonempty (SupportedLocalizationLattice P Z N) := by
  obtain ⟨L, hL, hloc, hs⟩ := exists_supported_lattice P Z hN
  exact ⟨⟨L, hL, hs.2, hloc⟩⟩

end SerrePositivity
