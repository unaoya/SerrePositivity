module
public import SerrePositivity.KTheory.G0Localization
public import SerrePositivity.CommutativeAlgebra.Support.Closed

/-! # A localization kernel element comes from one smaller closed support -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

variable (P : Submonoid R) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
/-- An element can be represented on the vanishing locus of one denominator. -/
def HasPrincipalLocalizationSupport (x : G0WithSupport Z) : Prop :=
  ∃ s ∈ P, ∃ y : G0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
    G0WithSupport.enlarge inf_le_left y = x

namespace HasPrincipalLocalizationSupport
variable {P Z}
lemma zero : HasPrincipalLocalizationSupport P Z 0 :=
  ⟨1, P.one_mem, 0, map_zero _⟩

lemma neg {x : G0WithSupport Z} (hx : HasPrincipalLocalizationSupport P Z x) :
    HasPrincipalLocalizationSupport P Z (-x) := by
  obtain ⟨s, hs, y, hy⟩ := hx
  exact ⟨s, hs, -y, by rw [map_neg, hy]⟩

lemma add {x x' : G0WithSupport Z} (hx : HasPrincipalLocalizationSupport P Z x)
    (hx' : HasPrincipalLocalizationSupport P Z x') :
    HasPrincipalLocalizationSupport P Z (x + x') :=
  principalSupport_add (fun W => G0WithSupport W) (fun h => G0WithSupport.enlarge h)
    (fun h h' y => DFunLike.congr_fun (G0WithSupport.enlarge_comp h h') y) hx hx'

lemma mk_torsion (M : SupportedFGModuleOn Z) (h : Module.IsTorsion' M.obj P) :
    HasPrincipalLocalizationSupport P Z (G0WithSupport.mk M) := by
  obtain ⟨s, hs, hM⟩ := exists_annihilator_supportedOn M h
  refine ⟨s, hs, G0WithSupport.mk ⟨M.obj, hM⟩, ?_⟩
  rw [G0WithSupport.enlarge_mk]
end HasPrincipalLocalizationSupport

/-- These elements form a subgroup: products combine the finitely many denominators. -/
def principalLocalizationSupportSubgroup : AddSubgroup (G0WithSupport Z) where
  carrier := {x | HasPrincipalLocalizationSupport P Z x}
  zero_mem' := HasPrincipalLocalizationSupport.zero
  add_mem' := HasPrincipalLocalizationSupport.add
  neg_mem' := HasPrincipalLocalizationSupport.neg

lemma localizationTorsionSubgroup_le_principalSupport :
    localizationTorsionSubgroup P Z ≤ principalLocalizationSupportSubgroup P Z := by
  rw [localizationTorsionSubgroup, AddSubgroup.closure_le]
  rintro x ⟨M, hM, rfl⟩
  exact HasPrincipalLocalizationSupport.mk_torsion M hM


/-- A finite module supported on a principal zero locus is torsion after inversion. -/
lemma moduleSTorsion_of_support_principal {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {s : R} (hs : s ∈ P)
    (h : Module.support R M ⊆ supportZeroLocus (Ideal.span ({s} : Set R))) :
    Module.IsTorsion' M P := by
  rw [isTorsion'_iff_forall]
  change Module.support R M ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({s} : Set R)) at h
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at h
  obtain ⟨n, hn⟩ := h (Ideal.subset_span (Set.mem_singleton s))
  exact fun m => ⟨s ^ n, P.pow_mem hs n, Module.mem_annihilator.mp hn m⟩

namespace G0WithSupport
variable {P Z} {B : Type u} [CommRing B] [Algebra R B] [IsLocalization P B]
  [IsNoetherianRing R]
/-- Every kernel element comes from one closed support cut out by a denominator. -/
lemma localize_kernel_supported (x : G0WithSupport Z)
    (hx : localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl x = 0) :
    ∃ s ∈ P, ∃ y : G0WithSupport (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      enlarge inf_le_left y = x := by
  apply localizationTorsionSubgroup_le_principalSupport P Z
  rw [← localize_ker (B := B) P Z]
  exact hx

omit [IsNoetherianRing R] in
/-- The image of a support cut by an inverted element is annihilated by localization. -/
lemma localize_enlarge_principal_eq_zero {s : R} (hs : s ∈ P) :
    (localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl).comp
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)) = 0 := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, enlarge_mk, AddMonoidHom.zero_apply]
  apply localize_mk_eq_zero
  exact moduleSTorsion_of_support_principal P hs (fun p hp => (M.property.2 hp).2)

/-- For one element, the supported localization sequence is right exact. -/
lemma localize_away_kernel_range (s : R) [IsLocalization.Away s B] :
    (localize (S := B) (Submonoid.powers s) Z
      (supportPullback (algebraMap R B) Z) le_rfl).ker =
    (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
      from inf_le_left)).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, y, hy⟩ := localize_kernel_supported (P := Submonoid.powers s) (B := B) x hx
    obtain ⟨n, rfl⟩ := ht
    refine ⟨enlarge (inf_le_inf_left Z (supportZeroLocus_pow_le s n)) y, ?_⟩
    rw [← AddMonoidHom.comp_apply, enlarge_comp]
    exact hy
  · rintro x ⟨y, rfl⟩
    exact DFunLike.congr_fun
      (localize_enlarge_principal_eq_zero (P := Submonoid.powers s) (B := B)
        (Submonoid.mem_powers s)) y

end G0WithSupport
end SerrePositivity
