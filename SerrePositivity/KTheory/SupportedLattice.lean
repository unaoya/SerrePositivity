module
public import SerrePositivity.KTheory.TorsionAnnihilator
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

/-- Every element becomes an element of the submodule after multiplication by a denominator. -/
def IsLocalizationLattice (L : Submodule R N) : Prop :=
  ∀ n : N, ∃ s : P, (s : R) • n ∈ L

include B in
/-- A denominator-clearing condition exhibits the inclusion as a module localization. -/
lemma IsLocalizationLattice.isLocalizedModule {L : Submodule R N}
    (h : IsLocalizationLattice P L) : IsLocalizedModule P L.subtype := by
  have hid := isLocalizedModule_id P N B
  refine ⟨fun s => hid.map_units s, ?_, ?_⟩
  · intro n
    obtain ⟨s, hs⟩ := h n
    exact ⟨(⟨(s : R) • n, hs⟩, s), rfl⟩
  · intro x y he
    exact ⟨1, by simpa using Subtype.ext he⟩

/-- Denominators can be cleared on the localized span of any set. -/
lemma isLocalizationLattice_span (t : Set N) (ht : Submodule.span B t = ⊤) :
    IsLocalizationLattice P (Submodule.span R t) := by
  intro n
  have hn : n ∈ Submodule.span B t := by rw [ht]; trivial
  induction hn using Submodule.span_induction with
  | mem n hn => exact ⟨1, by simpa using Submodule.subset_span hn⟩
  | zero => exact ⟨1, by simp⟩
  | add n m hn hm en em =>
    obtain ⟨s, hs⟩ := en
    obtain ⟨t, ht⟩ := em
    refine ⟨s * t, ?_⟩
    change ((s : R) * (t : R)) • (n + m) ∈ Submodule.span R _
    rw [smul_add]
    apply Submodule.add_mem
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hs
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ ht
  | smul b n hn en =>
    obtain ⟨s, hs⟩ := en
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj P b
    refine ⟨t * s, ?_⟩
    change ((t : R) * (s : R)) • (b • n) ∈ Submodule.span R _
    have hmul : (t : R) • (b • n) = r • n := by
      rw [← algebraMap_smul B (t : R), smul_smul, mul_comm, he, algebraMap_smul]
    rw [mul_comm, mul_smul, hmul, smul_comm]
    exact Submodule.smul_mem _ r hs

/-- Finite localized modules have finite lattices; support will be added below. -/
lemma exists_finite_lattice [Module.Finite B N] :
    ∃ L : Submodule R N, L.FG ∧ IsLocalizationLattice P L := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := B) (M := N)
  exact ⟨Submodule.span R (t : Set N), Submodule.fg_span t.finite_toSet,
    isLocalizationLattice_span P _ ht⟩

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


include B in
/-- The lattice inclusion gives the expected tensor-product identification. -/
def IsLocalizationLattice.tensorEquiv {L : Submodule R N}
    (h : IsLocalizationLattice P L) : B ⊗[R] L ≃ₗ[B] N := by
  have := h.isLocalizedModule (B := B)
  exact (IsLocalizedModule.isBaseChange P B L.subtype).equiv

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
