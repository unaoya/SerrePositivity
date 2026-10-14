module
public import SerrePositivity.KTheory.LatticeExact

/-! # Localization of supported G₀ via finite lattices -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
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

/-- Bridge the bundled scalar extension to the usual algebra tensor product. -/
def moduleCatBaseChangeTensorEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R B)).obj M ≃ₗ[B] B ⊗[R] M := by
  let φ := algebraMap R B
  have hφ : φ.toAlgebra = (inferInstance : Algebra R B) := toAlgebra_algebraMap
  have e : letI : Algebra R B := φ.toAlgebra
      (ModuleCat.extendScalars φ).obj M ≃ₗ[B] B ⊗[R] M := by
    exact LinearEquiv.refl B _
  rw [hφ] at e
  exact e

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
    IsModuleSTorsion P (sourceLocalizationMap (B := B) Z M).ker := by
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
