module
public import SerrePositivity.KTheory.SupportedLattice

/-! # Independence of the supported lattice class modulo torsion -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
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
