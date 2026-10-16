module
public import SerrePositivity.DifferentialGraded.Derived.TensorComputationNaturality

/-! # 両変数局所化の比較自然同型と具体的計算の可換図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 局所化前の比較は、厳密な因子化で輸送した固定左加群の比較と一致する。 -/
lemma moduleResolutionDerivedTensorBifunctorIso_fac
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L) ≫
          (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D S L)).hom =
      (eqToIso (moduleResolutionDerivedTensorBifunctor_obj A D R L)).hom ≫
        (moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L)).hom := by
  rw [moduleResolutionDerivedTensorBifunctorIso_hom_app]
  dsimp only [moduleResolutionDerivedTensorBifunctorFacIso, eqToIso]
  simp only [eqToHom_app, eqToHom_refl, Category.comp_id,
    moduleResolutionDerivedTensorLeftIso_hom_app]
  rfl

/-- 両変数導来tensorの解像度族変更は実際のtensor比較射による計算と可換。 -/
lemma moduleResolutionDerivedTensorBifunctorComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L)).app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorBifunctorComputation A D S L M).hom =
      (moduleResolutionDerivedTensorBifunctorComputation A D R L M).hom ≫
        (moduleProjectiveResolutionTensorIso A D (R M) (S M)
          (ForgetEnrichment.to (Complex A) L)).hom := by
  have h := NatTrans.congr_app (moduleResolutionDerivedTensorBifunctorIso_fac A D R S L)
    ((moduleToDerived A D).obj M)
  simp only [NatTrans.comp_app] at h
  dsimp only [moduleResolutionDerivedTensorBifunctorComputation, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, h, Category.assoc,
    moduleResolutionDerivedTensorComputation_choice, ← Category.assoc]

/-- 任意の個別解像度で計算すると、解像度族変更はその同じ計算値で一致する。 -/
lemma moduleTensorBifunctorResolutionComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    ((moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app
        ((leftModuleToDerived A D).obj L)).app ((moduleToDerived A D).obj M) ≫
        (moduleTensorBifunctorResolutionComputation A D S L P).hom =
      (moduleTensorBifunctorResolutionComputation A D R L P).hom := by
  dsimp only [moduleTensorBifunctorResolutionComputation, Iso.trans_hom]
  rw [← Category.assoc, moduleResolutionDerivedTensorBifunctorComputation_choice,
    Category.assoc, ← Iso.trans_hom, moduleProjectiveResolutionTensorIso_trans]

end SerrePositivity.DifferentialGraded
