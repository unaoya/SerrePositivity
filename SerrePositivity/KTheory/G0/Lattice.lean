module

public import SerrePositivity.KTheory.G0.Torsion
public import SerrePositivity.CommutativeAlgebra.Localization.Lattice
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.KTheory.G0.Basic

/-! # 局所化された加群の中の有限な台つき格子

## 概要

局所化された加群の中の有限な台つき格子を作り、その類がねじれを法として格子の選び方によらないことと、短完全列に対する格子の取り方を与える。

## 方針

二つの格子の差は局所化でねじれる加群なので、その類はねじれ部分群に入る。

## 規約

格子の存在には有限生成性を使う。

## 使われ方

`G0/Localization`（局所化の完全列）。
-/

@[expose] public noncomputable section

universe u

section SupportedLatticePart

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
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

end SupportedLatticePart

section LatticeClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R] (P : Submonoid R)
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

abbrev LocalizationG0Quotient := G0WithSupport Z ⧸ localizationTorsionSubgroup P Z

namespace LocalizationG0Quotient
variable {P Z}
/-- The class of a supported module modulo localization torsion. -/
def mk (M : SupportedFGModuleOn Z) : LocalizationG0Quotient P Z :=
  QuotientAddGroup.mk' (localizationTorsionSubgroup P Z) (G0WithSupport.mk M)

lemma mk_iso {M N : SupportedFGModuleOn Z} (e : M.obj ≅ N.obj) : mk (P := P) M = mk (P := P) N := by
  unfold mk
  rw [G0WithSupport.mk_iso e]

lemma mk_torsion (M : SupportedFGModuleOn Z) (h : Module.IsTorsion' M.obj P) : mk (P := P) M = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (mk_mem_localizationTorsionSubgroup P Z M h)

lemma mk_shortExact (E : SupportedModuleShortExact Z) :
    mk (P := P) E.middle = mk (P := P) E.left + mk (P := P) E.right := by
  unfold mk
  rw [G0WithSupport.mk_shortExact, map_add]
end LocalizationG0Quotient

variable {P Z} {N : Type u} [AddCommGroup N] [Module R N]
namespace SupportedLocalizationLattice
/-- If one lattice is contained in another, their quotient is localization torsion. -/
lemma quotient_torsion (L U : SupportedLocalizationLattice P Z N) (h : L.carrier ≤ U.carrier) :
    Module.IsTorsion' (U.carrier ⧸ LinearMap.range (Submodule.inclusion h)) P := by
  rw [isTorsion'_iff_forall]
  intro x
  obtain ⟨n, rfl⟩ := (LinearMap.range (Submodule.inclusion h)).mkQ_surjective x
  obtain ⟨s, hs⟩ := L.denominators n
  refine ⟨s, s.property, ?_⟩
  rw [← map_smul]
  change ((s : R) • n) ∈ (LinearMap.range (Submodule.inclusion h)).mkQ.ker
  rw [Submodule.ker_mkQ]
  exact ⟨⟨(s : R) • (n : N), hs⟩, Subtype.ext rfl⟩

/-- A lattice inclusion and its quotient form a supported short exact sequence. -/
def inclusionShortExact (L U : SupportedLocalizationLattice P Z N)
    (h : L.carrier ≤ U.carrier) : SupportedModuleShortExact Z where
  left := L.obj
  middle := U.obj
  right := ⟨ModuleCat.of R (U.carrier ⧸ LinearMap.range (Submodule.inclusion h)),
    U.obj.property.quotient _⟩
  f := Submodule.inclusion h
  g := (LinearMap.range (Submodule.inclusion h)).mkQ
  injective := Submodule.inclusion_injective h
  exact := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  surjective := Submodule.mkQ_surjective _

lemma class_eq_of_le (L U : SupportedLocalizationLattice P Z N) (h : L.carrier ≤ U.carrier) :
    LocalizationG0Quotient.mk (P := P) L.obj = LocalizationG0Quotient.mk (P := P) U.obj := by
  have he := LocalizationG0Quotient.mk_shortExact (P := P) (L.inclusionShortExact U h)
  have ht := LocalizationG0Quotient.mk_torsion
    (L.inclusionShortExact U h).right (L.quotient_torsion U h)
  rw [ht, add_zero] at he
  simpa only [inclusionShortExact] using he.symm

variable {N' : Type u} [AddCommGroup N'] [Module R N']
/-- Transport a supported lattice along a linear isomorphism of ambient modules. -/
def transport (L : SupportedLocalizationLattice P Z N) (e : N ≃ₗ[R] N') :
    SupportedLocalizationLattice P Z N' where
  carrier := L.carrier.map e.toLinearMap
  fg := L.fg.map e.toLinearMap
  support := by
    rw [← (e.ofSubmodules L.carrier (L.carrier.map e.toLinearMap) rfl).support_eq]
    exact L.support
  denominators n := by
    obtain ⟨s, hs⟩ := L.denominators (e.symm n)
    refine ⟨s, Submodule.mem_map.mpr ⟨(s : R) • e.symm n, hs, ?_⟩⟩
    simp

lemma class_transport (L : SupportedLocalizationLattice P Z N) (e : N ≃ₗ[R] N') :
    LocalizationG0Quotient.mk (P := P) (L.transport e).obj =
      LocalizationG0Quotient.mk (P := P) L.obj := by
  apply LocalizationG0Quotient.mk_iso
  exact (e.ofSubmodules L.carrier (L.carrier.map e.toLinearMap) rfl).symm.toModuleIso

variable {B : Type u} [CommRing B] [Algebra R B]
  [Module B N] [IsScalarTower R B N] [Module.Finite B N] [IsNoetherianRing R]

/-- The sum is a common finite supported lattice. -/
def sup (L U : SupportedLocalizationLattice P Z N)
    (hN : Module.support B N ⊆ supportPullback (algebraMap R B) Z) :
    SupportedLocalizationLattice P Z N where
  carrier := L.carrier ⊔ U.carrier
  fg := L.fg.sup U.fg
  support := (finite_lattice_supportedOn (B := B) Z hN _ (L.fg.sup U.fg)).2
  denominators n := by
    obtain ⟨s, hs⟩ := L.denominators n
    exact ⟨s, (show L.carrier ≤ L.carrier ⊔ U.carrier from le_sup_left) hs⟩

/-- The class modulo torsion is independent of the choice of a supported lattice. -/
lemma class_eq (L U : SupportedLocalizationLattice P Z N)
    (hN : Module.support B N ⊆ supportPullback (algebraMap R B) Z) :
    LocalizationG0Quotient.mk (P := P) L.obj = LocalizationG0Quotient.mk (P := P) U.obj := by
  exact (L.class_eq_of_le (L.sup U hN) le_sup_left).trans
    (U.class_eq_of_le (L.sup U hN) le_sup_right).symm
end SupportedLocalizationLattice
end SerrePositivity

end LatticeClassPart

section LatticeExactPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {P : Submonoid R} {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
  {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]

namespace SupportedLocalizationLattice
/-- The preimage of the middle lattice under the injective map. -/
def preimage (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (hf : Function.Injective f) : SupportedLocalizationLattice P Z N₁ := by
  let F : L.carrier.comap f →ₗ[R] L.carrier := f.restrict (fun _ h => h)
  have hi : Function.Injective F := submoduleRestriction_injective L.carrier f hf
  have : Module.Finite R (L.carrier.comap f) := Module.Finite.of_injective F hi
  refine ⟨L.carrier.comap f, Module.Finite.iff_fg.mp inferInstance,
    (Module.support_subset_of_injective F hi).trans L.support, ?_⟩
  intro n
  obtain ⟨s, hs⟩ := L.denominators (f n)
  exact ⟨s, by simpa only [Submodule.mem_comap, map_smul] using hs⟩

/-- The image of the middle lattice under the surjective map. -/
def image (L : SupportedLocalizationLattice P Z N₂)
    (g : N₂ →ₗ[R] N₃) (hg : Function.Surjective g) : SupportedLocalizationLattice P Z N₃ := by
  let G : L.carrier →ₗ[R] L.carrier.map g :=
    g.restrict (fun _ h => Submodule.mem_map_of_mem h)
  have hs : Function.Surjective G := submoduleImage_restrict_surjective L.carrier g
  refine ⟨L.carrier.map g, L.fg.map g,
    (Module.support_subset_of_surjective G hs).trans L.support, ?_⟩
  intro n
  obtain ⟨m, rfl⟩ := hg n
  obtain ⟨s, hs⟩ := L.denominators m
  exact ⟨s, Submodule.mem_map.mpr ⟨(s : R) • m, hs, g.map_smul _ _⟩⟩

/-- Pullback and image give a short exact sequence of finite supported lattices. -/
def shortExact (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g) :
    SupportedModuleShortExact Z := by
  let F : (L.preimage f hf).carrier →ₗ[R] L.carrier := f.restrict (fun _ h => h)
  let G : L.carrier →ₗ[R] (L.image g hg).carrier :=
    g.restrict (fun _ h => Submodule.mem_map_of_mem h)
  refine
    { left := (L.preimage f hf).obj
      middle := L.obj
      right := (L.image g hg).obj
      f := F
      g := G
      injective := submoduleRestriction_injective L.carrier f hf
      exact := submoduleRestriction_exact L.carrier f g he
      surjective := submoduleImage_restrict_surjective L.carrier g }

/-- Additivity for the lattices obtained by preimage and image. -/
lemma class_shortExact (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g) :
    LocalizationG0Quotient.mk (P := P) L.obj =
      LocalizationG0Quotient.mk (P := P) (L.preimage f hf).obj +
        LocalizationG0Quotient.mk (P := P) (L.image g hg).obj := by
  simpa only [shortExact] using
    LocalizationG0Quotient.mk_shortExact (P := P) (L.shortExact f g hf he hg)
end SupportedLocalizationLattice
end SerrePositivity

end LatticeExactPart
