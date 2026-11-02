module

public import SerrePositivity.KTheory.G0.Lattice
public import SerrePositivity.HomologicalAlgebra.ModuleBaseChangeTensor
public import SerrePositivity.CommutativeAlgebra.Support.Closed

/-! # 有限な格子による台つき G₀ の局所化

## 概要

台つき G₀ の局所化の写像を有限な格子で作り、その全射性と、核の元が一つ小さな閉台から来ることを示す（局所化の完全列）。

## 方針

局所化された加群に格子を取り、類がねじれを法として一意であることから写像を定める。

## 規約

局所化の完全列は G₀・K₀・係数つきの版が並行しており、一本化は保留（refactor-plan §6.2.3）。

## 使われ方

KTheory/Adams の重みの分解、`K0Localization`。
-/

@[expose] public noncomputable section

universe u

section G0LocalizationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
variable {R B : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
  (P : Submonoid R) [IsLocalization P B]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- Choose a supported lattice, with its class later shown independent of the choice. -/
def chosenSupportedLattice (N : SupportedFGModuleOn (supportPullback (algebraMap R B) Z)) :
    SupportedLocalizationLattice P Z N.obj :=
  Classical.choice (nonempty_supportedLocalizationLattice (B := B) P Z N.property.2)

/-- The inverse localization evaluation on module objects. -/
def supportedLatticeClass (N : SupportedFGModuleOn (supportPullback (algebraMap R B) Z)) :
    LocalizationG0Quotient P Z :=
  LocalizationG0Quotient.mk (chosenSupportedLattice P Z N).obj

lemma supportedLatticeClass_eq
    (N : SupportedFGModuleOn (supportPullback (algebraMap R B) Z))
    (L : SupportedLocalizationLattice P Z N.obj) :
    supportedLatticeClass P Z N = LocalizationG0Quotient.mk (P := P) L.obj :=
  (chosenSupportedLattice P Z N).class_eq L N.property.2

lemma supportedLatticeClass_iso
    {N N' : SupportedFGModuleOn (supportPullback (algebraMap R B) Z)} (e : N.obj ≅ N'.obj) :
    supportedLatticeClass P Z N = supportedLatticeClass P Z N' := by
  let L := chosenSupportedLattice P Z N
  let eR := e.toLinearEquiv.restrictScalars R
  exact ((supportedLatticeClass_eq P Z N' (L.transport eR)).trans
    (L.class_transport eR)).symm

lemma supportedLatticeClass_shortExact
    (E : SupportedModuleShortExact (supportPullback (algebraMap R B) Z)) :
    supportedLatticeClass P Z E.middle =
      supportedLatticeClass P Z E.left + supportedLatticeClass P Z E.right := by
  let L := chosenSupportedLattice P Z E.middle
  let f := E.f.restrictScalars R
  let g := E.g.restrictScalars R
  rw [supportedLatticeClass_eq P Z E.left (L.preimage f E.injective),
    supportedLatticeClass_eq P Z E.right (L.image g E.surjective)]
  exact L.class_shortExact f g E.injective E.exact E.surjective

/-- The inverse candidate, obtained from the universal property of G₀. -/
def g0LocalizationInverse : G0WithSupport (supportPullback (algebraMap R B) Z) →+
    LocalizationG0Quotient P Z :=
  G0WithSupport.lift (supportedLatticeClass P Z)
    (supportedLatticeClass_iso P Z) (supportedLatticeClass_shortExact P Z)

@[simp] lemma g0LocalizationInverse_mk
    (N : SupportedFGModuleOn (supportPullback (algebraMap R B) Z)) :
    g0LocalizationInverse P Z (G0WithSupport.mk N) = supportedLatticeClass P Z N :=
  G0WithSupport.lift_mk ..

/-- Localization factors through the quotient by torsion classes. -/
def g0LocalizationQuotientMap : LocalizationG0Quotient P Z →+
    G0WithSupport (supportPullback (algebraMap R B) Z) :=
  QuotientAddGroup.lift _ (G0WithSupport.localize P Z _ le_rfl)
    (G0WithSupport.localizationTorsionSubgroup_le_ker _ le_rfl)

omit [IsNoetherianRing R] in
@[simp] lemma g0LocalizationQuotientMap_mk (M : SupportedFGModuleOn Z) :
    g0LocalizationQuotientMap (B := B) P Z (LocalizationG0Quotient.mk (P := P) M) =
      G0WithSupport.localize P Z _ le_rfl (G0WithSupport.mk M) := by
  unfold g0LocalizationQuotientMap LocalizationG0Quotient.mk
  exact QuotientAddGroup.lift_mk _ _ _

omit [IsNoetherianRing R] in
lemma localize_lattice_mk
    (N : SupportedFGModuleOn (supportPullback (algebraMap R B) Z))
    (L : SupportedLocalizationLattice P Z N.obj) :
    G0WithSupport.localize P Z _ le_rfl (G0WithSupport.mk L.obj) = G0WithSupport.mk N := by
  rw [G0WithSupport.localize_mk]
  apply G0WithSupport.mk_iso
  exact ((moduleCatBaseChangeTensorEquiv L.obj.obj).trans
    (L.denominators.tensorEquiv (B := B))).toModuleIso

lemma g0LocalizationQuotientMap_inverse :
    (g0LocalizationQuotientMap (B := B) P Z).comp (g0LocalizationInverse P Z) =
      AddMonoidHom.id (G0WithSupport (supportPullback (algebraMap R B) Z)) := by
  apply G0WithSupport.hom_ext
  intro N
  simp only [AddMonoidHom.comp_apply, g0LocalizationInverse_mk,
    supportedLatticeClass, g0LocalizationQuotientMap_mk, AddMonoidHom.id_apply]
  exact localize_lattice_mk P Z N (chosenSupportedLattice P Z N)

/-- Augmentation into the actual bundled scalar extension. -/
def sourceLocalizationMap (M : SupportedFGModuleOn Z) : M.obj →ₗ[R]
    (M.baseChange (algebraMap R B) Z (supportPullback (algebraMap R B) Z) le_rfl).obj :=
  ((moduleCatBaseChangeTensorEquiv M.obj).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.mk R B M.obj 1)

instance sourceLocalizationMap_isLocalizedModule (M : SupportedFGModuleOn Z) :
    IsLocalizedModule P (sourceLocalizationMap (B := B) Z M) := by
  unfold sourceLocalizationMap
  infer_instance

/-- The image of a finite source module is a supported lattice in its localization. -/
def sourceImageLattice (M : SupportedFGModuleOn Z) : SupportedLocalizationLattice P Z
    (M.baseChange (algebraMap R B) Z (supportPullback (algebraMap R B) Z) le_rfl).obj := by
  let f := sourceLocalizationMap (B := B) Z M
  refine ⟨f.range, ?_, ?_, ?_⟩
  · exact Module.Finite.iff_fg.mp inferInstance
  · exact (Module.support_subset_of_surjective f.rangeRestrict f.surjective_rangeRestrict).trans
      M.property.2
  · intro n
    obtain ⟨⟨m, s⟩, he⟩ := IsLocalizedModule.surj P f n
    exact ⟨s, ⟨m, he.symm⟩⟩

omit [IsNoetherianRing R] in
lemma sourceLocalizationMap_kernel_torsion (M : SupportedFGModuleOn Z) :
    Module.IsTorsion' (sourceLocalizationMap (B := B) Z M).ker P := by
  rw [isTorsion'_iff_forall]
  intro m
  obtain ⟨r, hr, he⟩ := (IsLocalizedModule.mem_ker_iff P).mp m.property
  exact ⟨r, hr, Subtype.ext he⟩

/-- Source, torsion kernel, and image form a supported short exact sequence. -/
def sourceImageShortExact (M : SupportedFGModuleOn Z) : SupportedModuleShortExact Z := by
  let f := sourceLocalizationMap (B := B) Z M
  refine
    { left := ⟨ModuleCat.of R f.ker, M.property.submodule f.ker⟩
      middle := M
      right := (sourceImageLattice (B := B) P Z M).obj
      f := f.ker.subtype
      g := f.rangeRestrict
      injective := f.ker.subtype_injective
      exact := ?_
      surjective := f.surjective_rangeRestrict }
  intro m
  constructor
  · intro hm
    have hm' : f m = 0 := congrArg Subtype.val hm
    exact ⟨⟨m, hm'⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    exact m.property

lemma sourceImageLattice_class (M : SupportedFGModuleOn Z) :
    LocalizationG0Quotient.mk (P := P) (sourceImageLattice (B := B) P Z M).obj =
      LocalizationG0Quotient.mk (P := P) M := by
  have he := LocalizationG0Quotient.mk_shortExact (P := P) (sourceImageShortExact (B := B) P Z M)
  have ht := LocalizationG0Quotient.mk_torsion (sourceImageShortExact (B := B) P Z M).left
    (sourceLocalizationMap_kernel_torsion (B := B) P Z M)
  rw [ht, zero_add] at he
  simpa only [sourceImageShortExact] using he.symm

lemma g0LocalizationInverse_localize_mk (M : SupportedFGModuleOn Z) :
    g0LocalizationInverse P Z
      (G0WithSupport.localize (S := B) P Z _ le_rfl (G0WithSupport.mk M)) =
        LocalizationG0Quotient.mk (P := P) M := by
  rw [G0WithSupport.localize_mk, g0LocalizationInverse_mk,
    supportedLatticeClass_eq P Z _ (sourceImageLattice (B := B) P Z M), sourceImageLattice_class]

lemma g0LocalizationInverse_quotientMap :
    (g0LocalizationInverse P Z).comp (g0LocalizationQuotientMap (B := B) P Z) =
      AddMonoidHom.id (LocalizationG0Quotient P Z) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply G0WithSupport.hom_ext
  intro M
  change g0LocalizationInverse P Z
      (g0LocalizationQuotientMap (B := B) P Z (LocalizationG0Quotient.mk (P := P) M)) =
    LocalizationG0Quotient.mk (P := P) M
  rw [g0LocalizationQuotientMap_mk, g0LocalizationInverse_localize_mk]

/-- Supported G₀ after localization is the quotient by torsion classes. -/
def g0LocalizationQuotientEquiv : LocalizationG0Quotient P Z ≃+
    G0WithSupport (supportPullback (algebraMap R B) Z) where
  toFun := g0LocalizationQuotientMap (B := B) P Z
  invFun := g0LocalizationInverse P Z
  left_inv x := DFunLike.congr_fun (g0LocalizationInverse_quotientMap P Z) x
  right_inv x := DFunLike.congr_fun (g0LocalizationQuotientMap_inverse P Z) x
  map_add' := map_add _

omit [IsNoetherianRing R] in
@[simp] lemma g0LocalizationQuotientMap_apply (x : G0WithSupport Z) :
    g0LocalizationQuotientMap (B := B) P Z
      (QuotientAddGroup.mk' (localizationTorsionSubgroup P Z) x) =
        G0WithSupport.localize (S := B) P Z _ le_rfl x := by
  exact QuotientAddGroup.lift_mk _ _ _

namespace G0WithSupport
/-- Localization is surjective for an arbitrary multiplicative set. -/
lemma localize_surjective : Function.Surjective
    (localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl) := by
  intro y
  obtain ⟨q, hq⟩ := (g0LocalizationQuotientEquiv (B := B) P Z).surjective y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (localizationTorsionSubgroup P Z) q
  exact ⟨x, (g0LocalizationQuotientMap_apply P Z x).symm.trans hq⟩

/-- The localization kernel consists exactly of torsion classes. -/
lemma localize_ker :
    (localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl).ker =
      localizationTorsionSubgroup P Z := by
  apply le_antisymm
  · intro x hx
    apply (QuotientAddGroup.eq_zero_iff x).mp
    apply (g0LocalizationQuotientEquiv (B := B) P Z).injective
    change g0LocalizationQuotientMap (B := B) P Z
        (QuotientAddGroup.mk' (localizationTorsionSubgroup P Z) x) =
      g0LocalizationQuotientMap (B := B) P Z 0
    rw [g0LocalizationQuotientMap_apply, map_zero]
    exact hx
  · exact localizationTorsionSubgroup_le_ker _ le_rfl
end G0WithSupport

end SerrePositivity

end G0LocalizationPart

section LocalizationKernelSupportPart

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

end LocalizationKernelSupportPart
