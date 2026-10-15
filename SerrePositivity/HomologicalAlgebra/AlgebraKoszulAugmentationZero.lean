module
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulAugmentation
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # The canonical dual Koszul augmentation is an isomorphism on degree-zero terms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
open DerivedCompletion
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- A cone term is its target term when its shifted source term vanishes. -/
def mappingConeInrTermIso {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (q : ℤ) (hK : IsZero (K.X (q + 1))) :
    L.X q ≅ (CochainComplex.mappingCone f).X q where
  hom := inrX f q
  inv := sndX f q
  hom_inv_id := inrX_sndX f q
  inv_hom_id := by
    apply ext_from_X f (q + 1) q rfl
    · exact hK.eq_of_src _ _
    · simp only [← Category.assoc, inrX_sndX, Category.id_comp]
      exact (Category.comp_id _).symm

/-- The standard Koszul inclusion identifies the actual degree-zero terms. -/
instance koszulComplexInclusion_f_zero_isIso : ∀ {e : ℕ} (z : Fin e → R),
    IsIso ((koszulComplexInclusion R z).f 0)
  | 0, z => by change IsIso (𝟙 _); infer_instance
  | e + 1, z => by
    have := koszulComplexInclusion_f_zero_isIso (Fin.init z)
    have : IsIso ((CochainComplex.mappingCone.inr
        (smulId (z (Fin.last e)) (koszulComplex (Fin.init z)))).f 0) :=
      (mappingConeInrTermIso
        (smulId (z (Fin.last e)) (koszulComplex (Fin.init z))) 0
        (koszulComplex_isZero_X_of_pos (Fin.init z) 1 (by omega))).isIso_hom
    change IsIso ((koszulComplexInclusion R (Fin.init z)).f 0 ≫ _)
    infer_instance

/-- Precomposition by an R-module isomorphism is an actual C-module isomorphism. -/
def algebraLinearYonedaPrecompIso {P Q : ModuleCat.{u} R} (e : P ≅ Q)
    (M : ModuleCat.{u} C) :
    ModuleCat.of C (Q ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) ≅
      ModuleCat.of C (P ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) where
  hom := ModuleCat.ofHom (algebraLinearYonedaPrecomp e.hom M)
  inv := ModuleCat.ofHom (algebraLinearYonedaPrecomp e.inv M)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change e.inv ≫ e.hom ≫ f = f
    simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change e.hom ≫ e.inv ≫ f = f
    simp

/-- Every finite-stage dual augmentation is an isomorphism on degree-zero terms. -/
instance algebraKoszulDualAugmentation_f_zero_isIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) : IsIso (((algebraKoszulDualAugmentation (C := C) z).app M).f 0) := by
  have : IsIso ((restrictionMap (koszulComplexInclusion R z) embUp).f 0) := by
    change IsIso ((koszulComplexInclusion R z).f 0)
    infer_instance
  exact (algebraLinearYonedaPrecompIso
    (asIso ((restrictionMap (koszulComplexInclusion R z) embUp).f 0)) M).isIso_hom

/-- For a connected sequential diagram, an isomorphic cocone is already its colimit. -/
lemma sequentialColimit_desc_isIso_of_components
    (F : ℕ ⥤ ModuleCat.{u} C) (c : Cocone F) [∀ n, IsIso (c.ι.app n)] :
    IsIso (colimit.desc F c) := by
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : IsIso c.ι := NatIso.isIso_of_isIso_app _
  have : IsIso (colimMap c.ι) :=
    inferInstanceAs (IsIso ((colim : (ℕ ⥤ ModuleCat.{u} C) ⥤ ModuleCat.{u} C).map c.ι))
  exact (colimit.isColimit F).nonempty_isColimit_iff_isIso_desc.mp
    ⟨c.isColimitOfIsIsoColimMapι⟩

/-- The canonical actual colimit augmentation is an isomorphism on its degree-zero terms. -/
instance algebraKoszulDualColimitAugmentation_f_zero_isIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) :
    IsIso (((algebraKoszulDualColimitAugmentationNatTrans (C := C) z).app M).f 0) := by
  let F : CochainComplex (ModuleCat.{u} C ⥤ ModuleCat.{u} C) ℕ ⥤ ModuleCat.{u} C :=
    eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) 0 ⋙
      (evaluation (ModuleCat.{u} C) (ModuleCat.{u} C)).obj M
  let c := F.mapCocone (algebraKoszulDualAugmentationCocone (C := C) z)
  have : ∀ n : ℕ, IsIso (c.ι.app n) := fun n =>
    algebraKoszulDualAugmentation_f_zero_isIso (fun j => z j ^ n) M
  have := sequentialColimit_desc_isIso_of_components _ c
  have h := preservesColimitIso_inv_comp_desc F
    (algebraKoszulDualFunctorComplexDiagram (C := C) z)
    (algebraKoszulDualAugmentationCocone (C := C) z)
  change IsIso (F.map (algebraKoszulDualColimitAugmentation (C := C) z))
  have heq : F.map (algebraKoszulDualColimitAugmentation (C := C) z) =
      (preservesColimitIso F (algebraKoszulDualFunctorComplexDiagram (C := C) z)).hom ≫
        colimit.desc _ c := by
    rw [← h]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      algebraKoszulDualColimitAugmentation]
  rw [heq]
  infer_instance

/-- The augmentation to the actual coefficient module is an isomorphism in degree zero. -/
instance algebraKoszulDualColimitToSingle_f_zero_isIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) :
    IsIso (((algebraKoszulDualColimitToSingle (C := C) z).app M).f 0) := by
  change IsIso
    ((((algebraKoszulDualColimitAugmentationNatTrans (C := C) z).app M).f 0) ≫
      (((algebraKoszulDualEmptyNatIso (R := R) (C := C)).hom.app M).f 0))
  infer_instance

/-- The actual integer augmentation likewise identifies the degree-zero terms. -/
instance algebraKoszulDualIntegerToSingle_f_zero_isIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) :
    IsIso (((algebraKoszulDualIntegerToSingle (C := C) z).app M).f 0) := by
  let g := (algebraKoszulDualColimitToSingle (C := C) z).app M
  have : IsIso ((extendMap g nonnegativeCochainEmbedding).f 0) := by
    rw [extendMap_f g nonnegativeCochainEmbedding
      (show nonnegativeCochainEmbedding.f 0 = 0 from rfl)]
    infer_instance
  change IsIso ((extendMap g nonnegativeCochainEmbedding).f 0 ≫
    (((nonnegativeSingleExtendNatIso (C := C)).hom.app M).f 0))
  infer_instance

end SerrePositivity
