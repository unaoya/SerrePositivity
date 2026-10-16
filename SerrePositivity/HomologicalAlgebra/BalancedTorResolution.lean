module
public import SerrePositivity.HomologicalAlgebra.ModuleTensorChainFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry

/-! # Natural computation of Tor by a fixed resolution of its left argument -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (P : ProjectiveResolution M)

/-- Use derived symmetry to resolve the fixed module rather than the varying module. -/
def moduleTensorChainRealizationIso (N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleFunctor M).obj N ≅
      DerivedCategory.Q.obj (((moduleTensorChainFunctor P.complex).obj N).extend embUp) :=
  DerivedCategory.Minus.ι.mapIso
      (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj M)
        (boundedAboveDerivedSingleFunctor.obj N)) ≪≫
    boundedAboveDerivedTensorModuleIso N M ≪≫ realizedDerivedTensorResolutionIso N P

/-- This fixed-resolution computation is natural in every morphism of the varying module. -/
lemma moduleTensorChainRealizationIso_naturality {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    (boundedAboveDerivedTensorModuleFunctor M).map f ≫
        (moduleTensorChainRealizationIso M P N').hom =
      (moduleTensorChainRealizationIso M P N).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.extendMap
          ((moduleTensorChainFunctor P.complex).map f) embUp) := by
  have hs := congrArg (fun k ↦ k.hom)
    (boundedAboveDerivedTensorSymmetry_naturality
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)) (boundedAboveDerivedSingleFunctor.map f))
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hs
  simp only [moduleTensorChainRealizationIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M))
      (boundedAboveDerivedSingleFunctor.map f))).hom ≫ _ = _
  rw [← Category.assoc]
  erw [hs]
  rw [Category.assoc]
  erw [reassoc_of% boundedAboveDerivedTensorModuleIso_naturality_left f M]
  rw [realizedDerivedTensorResolutionIso_naturality_left f P]
  rfl

/-- The comparison is a natural isomorphism before taking homology. -/
def moduleTensorChainRealizationNatIso :
    boundedAboveDerivedTensorModuleFunctor M ≅
      moduleTensorChainFunctor P.complex ⋙ embUp.extendFunctor (ModuleCat R) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (moduleTensorChainRealizationIso M P)
    (fun f ↦ moduleTensorChainRealizationIso_naturality M P f)

/-- Existing Tor is computed naturally by tensoring with one fixed projective resolution. -/
def torFixedResolutionNatIso (i : ℕ) :
    (Tor (ModuleCat R) i).obj M ≅
      moduleTensorChainFunctor P.complex ⋙ homologyFunctor (ModuleCat R) (.down ℕ) i :=
  (boundedAboveDerivedTensorModuleTorNatIso M i).symm ≪≫
    Functor.isoWhiskerRight (moduleTensorChainRealizationNatIso M P)
      (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleTensorChainFunctor P.complex)
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (embUp.extendFunctor (ModuleCat R))
          (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))) ≪≫
        extendChainHomologyIso R i)

end SerrePositivity
