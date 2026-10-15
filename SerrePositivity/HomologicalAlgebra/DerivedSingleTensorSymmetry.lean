module
public import SerrePositivity.HomologicalAlgebra.CochainAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps

/-! # The actual derived augmentation preserves symmetry and the derived algebra product commutes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual tensor augmentation preserves the standard signed derived symmetry. -/
lemma boundedAboveDerivedTensorModuleAugmentation_symmetry (M N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorSymmetry
        (boundedAboveDerivedSingleFunctor.obj M) (boundedAboveDerivedSingleFunctor.obj N)).hom.hom ≫
      (boundedAboveDerivedTensorModuleAugmentation N).app M =
    (boundedAboveDerivedTensorModuleAugmentation M).app N ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (β_ M N).hom := by
  let P := projectiveResolution M
  let Q := projectiveResolution N
  rw [boundedAboveDerivedTensorModuleAugmentation_models Q P,
    boundedAboveDerivedTensorModuleAugmentation_models P Q]
  rw [← Category.assoc, boundedAboveDerivedTensorSymmetry_models, Category.assoc]
  simp only [Category.assoc]
  change _ = (boundedAboveDerivedTensorModelIso
    (boundedAboveDerivedSingleFunctor.obj M) (boundedAboveDerivedSingleFunctor.obj N)
    (projectiveResolutionDerivedModel P) (projectiveResolutionDerivedModel Q)).hom ≫
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
      ((CochainComplex.singleFunctor (ModuleCat R) 0).map (β_ M N).hom)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply congrArg DerivedCategory.Q.map
  rw [← Category.assoc, ← cochainTensorSymmetry_naturality,
    Category.assoc, cochainSingleTensorIso_symmetry]
  rw [Category.assoc]

/-- The canonical actual derived multiplication of a commutative algebra commutes. -/
lemma boundedAboveDerivedAlgebraMul_comm
    (A : Type u) [CommRing A] [Algebra R A] :
    (boundedAboveDerivedTensorSymmetry
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom ≫
      boundedAboveDerivedAlgebraMul (R := R) A = boundedAboveDerivedAlgebraMul (R := R) A := by
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensorSymmetry
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom.hom ≫
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))) =
    (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))
  rw [← Category.assoc, boundedAboveDerivedTensorModuleAugmentation_symmetry,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hc : (β_ (ModuleCat.of R A) (ModuleCat.of R A)).hom ≫
      ModuleCat.ofHom (LinearMap.mul' R A) = ModuleCat.ofHom (LinearMap.mul' R A) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact mul_comm b a
  rw [hc]

end SerrePositivity
