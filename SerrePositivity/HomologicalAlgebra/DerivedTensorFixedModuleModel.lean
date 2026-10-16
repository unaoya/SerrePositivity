module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainFiltration
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry

/-! # Fixed right-module resolution, natural in every unresolved left module -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Compute the actual tensor M ⊗ᴸ C with C's original chosen resolution.
The comparison is built from the established module and resolution comparisons. -/
def derivedTensorFixedModuleModelIso (C M : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleFunctor M).obj C ≅
      DerivedCategory.Q.obj ((moduleTensorCochainFunctor
        (extRes (projectiveResolution C))).obj M) :=
  boundedAboveDerivedTensorModuleIso M C ≪≫
    realizedDerivedTensorResolutionIso M (projectiveResolution C) ≪≫
      (DerivedCategory.Q.mapIso
        (mapExtendIso (tensorLeft M) (projectiveResolution C).complex embUp)).symm

/-- The fixed-resolution computation keeps the actual map of the unresolved
module, including the ordinary reduction transitions used in KL. -/
@[reassoc] lemma derivedTensorFixedModuleModelIso_naturality
    (C : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj C)))).hom ≫
        (derivedTensorFixedModuleModelIso C N).hom =
      (derivedTensorFixedModuleModelIso C M).hom ≫
        DerivedCategory.Q.map ((moduleTensorCochainFunctor
          (extRes (projectiveResolution C))).map f) := by
  let P := projectiveResolution C
  let vM := DerivedCategory.Q.mapIso (mapExtendIso (tensorLeft M) P.complex embUp)
  let vN := DerivedCategory.Q.mapIso (mapExtendIso (tensorLeft N) P.complex embUp)
  let pf := DerivedCategory.Q.map ((moduleTensorCochainFunctor (extRes P)).map f)
  let qf := DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f)
      (.down ℕ)).app P.complex) embUp)
  have hv : pf ≫ vN.hom = vM.hom ≫ qf := by
    dsimp only [pf, vN, vM, qf, moduleTensorCochainFunctor, extRes]
    simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg DerivedCategory.Q.map
      (mapExtendIso_natTrans (tensorLeft M) P.complex embUp
        ((tensoringLeft (ModuleCat R)).map f))
  have hv' : qf ≫ vN.inv = vM.inv ≫ pf := by
    apply (cancel_epi vM.hom).mp
    rw [← Category.assoc, ← hv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have h₁ := boundedAboveDerivedTensorModuleIso_naturality_left f C
  have h₂ := realizedDerivedTensorResolutionIso_naturality_left f P
  simp only [derivedTensorFixedModuleModelIso, Iso.trans_hom, Iso.symm_hom]
  change _ ≫ (_ ≫ _ ≫ vN.inv) = (_ ≫ _ ≫ vM.inv) ≫ pf
  calc
    _ = ((boundedAboveDerivedTensorModuleIso M C).hom ≫
        (realizedDerivedTensorMapLeft R f).app C) ≫
          (realizedDerivedTensorResolutionIso N P).hom ≫ vN.inv := by
      rw [← Category.assoc, h₁]
    _ = (boundedAboveDerivedTensorModuleIso M C).hom ≫
        (realizedDerivedTensorResolutionIso M P).hom ≫ qf ≫ vN.inv := by
      rw [Category.assoc, ← Category.assoc ((realizedDerivedTensorMapLeft R f).app C), h₂]
      simp only [Category.assoc, qf]
    _ = _ := by rw [hv']; simp only [Category.assoc, P]

/-- Put the fixed coefficient C first, preserving the actual derived symmetry. -/
def derivedTensorCoefficientModelIso (C M : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
      DerivedCategory.Q.obj ((moduleTensorCochainFunctor
        (extRes (projectiveResolution C))).obj M) :=
  (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj M)) ≪≫ derivedTensorFixedModuleModelIso C M

/-- The fixed coefficient model is natural for every unresolved test-module map. -/
@[reassoc] lemma derivedTensorCoefficientModelIso_naturality
    (C : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (boundedAboveDerivedTensorModuleFunctor C).map f ≫
        (derivedTensorCoefficientModelIso C N).hom =
      (derivedTensorCoefficientModelIso C M).hom ≫
        DerivedCategory.Q.map ((moduleTensorCochainFunctor
          (extRes (projectiveResolution C))).map f) := by
  let sM := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj M))
  let sN := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj N))
  let d := (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f)
    (𝟙 (boundedAboveDerivedSingleFunctor.obj C)))).hom
  have hs : (boundedAboveDerivedTensorModuleFunctor C).map f ≫ sN.hom = sM.hom ≫ d := by
    have h := boundedAboveDerivedTensorSymmetry_naturality
      (𝟙 (boundedAboveDerivedSingleFunctor.obj C)) (boundedAboveDerivedSingleFunctor.map f)
    exact congrArg (fun g => (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).map g) h
  have hf := derivedTensorFixedModuleModelIso_naturality C f
  change _ ≫ (sN.hom ≫ _) = (sM.hom ≫ _) ≫ _
  rw [← Category.assoc, hs, Category.assoc, hf, ← Category.assoc]

/-- Changing the resolved coefficient uses the original chosen resolution lift. -/
@[reassoc] lemma derivedTensorFixedModuleModelIso_naturality_right
    (M : ModuleCat.{u} R) {C D : ModuleCat.{u} R} (f : C ⟶ D) :
    (boundedAboveDerivedTensorModuleFunctor M).map f ≫
        (derivedTensorFixedModuleModelIso D M).hom =
      (derivedTensorFixedModuleModelIso C M).hom ≫ DerivedCategory.Q.map
        (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
          (extLift (projectiveResolution C) f (projectiveResolution D))) := by
  let P := projectiveResolution C
  let Q := projectiveResolution D
  let vC := DerivedCategory.Q.mapIso (mapExtendIso (tensorLeft M) P.complex embUp)
  let vD := DerivedCategory.Q.mapIso (mapExtendIso (tensorLeft M) Q.complex embUp)
  let pf := DerivedCategory.Q.map (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
    (extLift P f Q))
  let qf := DerivedCategory.Q.map (HomologicalComplex.extendMap
    (((tensorLeft M).mapHomologicalComplex (.down ℕ)).map
      (ProjectiveResolution.lift f P Q)) embUp)
  have hv : pf ≫ vD.hom = vC.hom ≫ qf := by
    dsimp only [pf, vD, vC, qf, extLift]
    simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg DerivedCategory.Q.map
      (mapExtendIso_naturality (tensorLeft M) embUp (ProjectiveResolution.lift f P Q))
  have hv' : qf ≫ vD.inv = vC.inv ≫ pf := by
    apply (cancel_epi vC.hom).mp
    rw [← Category.assoc, ← hv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have h₁ := boundedAboveDerivedTensorModuleIso_naturality_right M f
  have h₂ := realizedDerivedTensorResolutionIso_naturality M f P Q
  simp only [derivedTensorFixedModuleModelIso, Iso.trans_hom, Iso.symm_hom]
  change _ ≫ (_ ≫ _ ≫ vD.inv) = (_ ≫ _ ≫ vC.inv) ≫ pf
  calc
    _ = ((boundedAboveDerivedTensorModuleIso M C).hom ≫
        (realizedDerivedTensorFunctor R M).map f) ≫
          (realizedDerivedTensorResolutionIso M Q).hom ≫ vD.inv := by
      rw [← Category.assoc, h₁]
    _ = (boundedAboveDerivedTensorModuleIso M C).hom ≫
        (realizedDerivedTensorResolutionIso M P).hom ≫ qf ≫ vD.inv := by
      rw [Category.assoc, ← Category.assoc ((realizedDerivedTensorFunctor R M).map f), h₂]
      simp only [Category.assoc, qf]
    _ = _ := by rw [hv']; simp only [Category.assoc, P]

/-- Naturality in the coefficient includes the actual multiplication maps that
define the Tor scalar endomorphisms in KL. -/
@[reassoc] lemma derivedTensorCoefficientModelIso_naturality_left
    (M : ModuleCat.{u} R) {C D : ModuleCat.{u} R} (f : C ⟶ D) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (derivedTensorCoefficientModelIso D M).hom =
      (derivedTensorCoefficientModelIso C M).hom ≫ DerivedCategory.Q.map
        (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
          (extLift (projectiveResolution C) f (projectiveResolution D))) := by
  let sC := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj M))
  let sD := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj D)
      (boundedAboveDerivedSingleFunctor.obj M))
  let d := (boundedAboveDerivedTensorModuleFunctor M).map f
  have hs : (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫ sD.hom = sC.hom ≫ d := by
    exact congrArg (fun g => (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).map g)
      (boundedAboveDerivedTensorSymmetry_naturality
        (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))
  have hf := derivedTensorFixedModuleModelIso_naturality_right M f
  change _ ≫ (sD.hom ≫ _) = (sC.hom ≫ _) ≫ _
  rw [← Category.assoc, hs, Category.assoc, hf, ← Category.assoc]

end SerrePositivity
