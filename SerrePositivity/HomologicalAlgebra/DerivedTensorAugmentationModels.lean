module
public import SerrePositivity.HomologicalAlgebra.CochainAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedTensorTriangle

/-! # Standard tensor augmentation on arbitrary projective derived models -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Any two projective derived models, with chain augmentations inducing their model isos,
compute the same established tensor augmentation.
Strict compatibility of chosen lifts is unnecessary. -/
lemma boundedAboveDerivedTensorModuleAugmentation_projective_models
    {M N : ModuleCat.{u} R}
    (P : BoundedAboveDerivedModel (boundedAboveDerivedSingleFunctor.obj M).obj)
    (Q : BoundedAboveDerivedModel (boundedAboveDerivedSingleFunctor.obj N).obj)
    (εP : P.complex ⟶ cochainSingleZero M) (εQ : Q.complex ⟶ cochainSingleZero N)
    (hεP : DerivedCategory.Q.map εP = P.iso.hom)
    (hεQ : DerivedCategory.Q.map εQ = Q.iso.hom) :
    (boundedAboveDerivedTensorModuleAugmentation M).app N =
      (boundedAboveDerivedTensorModelIso
        (boundedAboveDerivedSingleFunctor.obj M) (boundedAboveDerivedSingleFunctor.obj N)
        P Q).hom ≫
      DerivedCategory.Q.map (cochainTensorMap εP εQ ≫ (cochainSingleTensorIso M N).hom) := by
  let P₀ := projectiveResolutionDerivedModel (projectiveResolution M)
  let Q₀ := projectiveResolutionDerivedModel (projectiveResolution N)
  let f := P.map P₀ (𝟙 _)
  let g := Q.map Q₀ (𝟙 _)
  have hf : Homotopy (f ≫ projectiveResolutionCochainAugmentation (projectiveResolution M))
      εP := by
    apply homotopyOfDerivedMapEq
    rw [CategoryTheory.Functor.map_comp]
    change DerivedCategory.Q.map f ≫ P₀.iso.hom = DerivedCategory.Q.map εP
    rw [P.map_naturality, Category.comp_id, hεP]
  have hg : Homotopy (g ≫ projectiveResolutionCochainAugmentation (projectiveResolution N))
      εQ := by
    apply homotopyOfDerivedMapEq
    rw [CategoryTheory.Functor.map_comp]
    change DerivedCategory.Q.map g ≫ Q₀.iso.hom = DerivedCategory.Q.map εQ
    rw [Q.map_naturality, Category.comp_id, hεQ]
  have hn := boundedAboveDerivedTensorModelIso_naturality P P₀ Q Q₀
    (𝟙 (boundedAboveDerivedSingleFunctor.obj M))
    (𝟙 (boundedAboveDerivedSingleFunctor.obj N)) f g
    (P.map_naturality P₀ (𝟙 _)) (Q.map_naturality Q₀ (𝟙 _))
  simp only [← CategoryTheory.prod_id', CategoryTheory.Functor.map_id] at hn
  rw [ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  rw [boundedAboveDerivedTensorModuleAugmentation_chosen_models]
  change (boundedAboveDerivedTensorModelIso _ _ P₀ Q₀).hom ≫ _ = _
  rw [hn, Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [← Category.assoc, cochainTensorMap_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  congr 1
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R)
    ((cochainTensorHomotopyLeft hf _).trans (cochainTensorHomotopyRight εP hg))

/-- The actual derived tensor augmentation recovers the standard left unitor. -/
lemma boundedAboveDerivedTensorModuleAugmentation_leftUnitor (M : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R R)).app M ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (λ_ M).hom =
      (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedSingleFunctor.obj M)).hom.hom := by
  let P := projectiveResolutionDerivedModel (projectiveResolution M)
  have hu : DerivedCategory.Q.map (𝟙 (cochainTensorUnit (R := R))) =
      (boundedAboveDerivedTensorUnitModel (R := R)).iso.hom := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  erw [boundedAboveDerivedTensorModuleAugmentation_projective_models
    (M := ModuleCat.of R R) (N := M) boundedAboveDerivedTensorUnitModel P (𝟙 _)
    (projectiveResolutionCochainAugmentation
      (projectiveResolution M)) hu rfl]
  rw [boundedAboveDerivedLeftUnitor_models _ P]
  change (_ ≫ DerivedCategory.Q.map _) ≫ DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (ModuleCat R) 0).map (λ_ M).hom) =
    _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
      (projectiveResolutionCochainAugmentation (projectiveResolution M))
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  erw [cochainSingleTensorIso_leftUnitor M]
  exact MonoidalCategory.leftUnitor_naturality
    (projectiveResolutionCochainAugmentation (projectiveResolution M))

/-- The actual derived tensor augmentation recovers the standard right unitor. -/
lemma boundedAboveDerivedTensorModuleAugmentation_rightUnitor (M : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleAugmentation M).app (ModuleCat.of R R) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (ρ_ M).hom =
      (boundedAboveDerivedTensorRightUnitor (boundedAboveDerivedSingleFunctor.obj M)).hom.hom := by
  let P := projectiveResolutionDerivedModel (projectiveResolution M)
  have hu : DerivedCategory.Q.map (𝟙 (cochainTensorUnit (R := R))) =
      (boundedAboveDerivedTensorUnitModel (R := R)).iso.hom := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  erw [boundedAboveDerivedTensorModuleAugmentation_projective_models
    (M := M) (N := ModuleCat.of R R) P boundedAboveDerivedTensorUnitModel
    (projectiveResolutionCochainAugmentation
      (projectiveResolution M)) (𝟙 _) rfl hu]
  rw [boundedAboveDerivedRightUnitor_models _ P]
  change (_ ≫ DerivedCategory.Q.map _) ≫ DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (ModuleCat R) 0).map (ρ_ M).hom) =
    _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
      (projectiveResolutionCochainAugmentation (projectiveResolution M))
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  erw [cochainSingleTensorIso_rightUnitor M]
  exact MonoidalCategory.rightUnitor_naturality
    (projectiveResolutionCochainAugmentation (projectiveResolution M))

end SerrePositivity
