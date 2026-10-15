module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps

/-! # The actual derived algebra multiplication has its standard left and right unit -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual derived multiplication has the specified algebra-map unit on the left. -/
lemma boundedAboveDerivedAlgebraUnit_mul
    (A : Type u) [CommRing A] [Algebra R A] :
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedAlgebraUnit (R := R) A)
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))) ≫
      boundedAboveDerivedAlgebraMul (R := R) A =
    (boundedAboveDerivedTensorLeftUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom := by
  let u := ModuleCat.ofHom (Algebra.linearMap R A)
  have hu : boundedAboveDerivedAlgebraUnit (R := R) A =
      boundedAboveDerivedSingleFunctor.map u := by
    apply InducedCategory.hom_ext
    change (𝟙 _) ≫ _ = _
    exact Category.id_comp _
  rw [hu]
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map u)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))))).hom ≫
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (ModuleCat.ofHom (LinearMap.mul' R A))) =
    (boundedAboveDerivedTensorLeftUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom.hom
  rw [← Category.assoc, boundedAboveDerivedTensorModuleAugmentation_naturality_left,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hl : ((tensoringLeft (ModuleCat.{u} R)).map u).app (ModuleCat.of R A) ≫
      ModuleCat.ofHom (LinearMap.mul' R A) = (λ_ (ModuleCat.of R A)).hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro r
    apply LinearMap.ext
    intro a
    exact (Algebra.smul_def r a).symm
  rw [hl]
  exact boundedAboveDerivedTensorModuleAugmentation_leftUnitor (ModuleCat.of R A)

/-- The actual derived multiplication has the specified algebra-map unit on the right. -/
lemma boundedAboveDerivedAlgebraMul_unit
    (A : Type u) [CommRing A] [Algebra R A] :
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))
        (boundedAboveDerivedAlgebraUnit (R := R) A)) ≫
      boundedAboveDerivedAlgebraMul (R := R) A =
    (boundedAboveDerivedTensorRightUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom := by
  let u := ModuleCat.ofHom (Algebra.linearMap R A)
  have hu : boundedAboveDerivedAlgebraUnit (R := R) A =
      boundedAboveDerivedSingleFunctor.map u := by
    apply InducedCategory.hom_ext
    change (𝟙 _) ≫ _ = _
    exact Category.id_comp _
  have hn := (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).naturality u
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))
      (boundedAboveDerivedSingleFunctor.map u))).hom ≫
      (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) =
    (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R R) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        ((tensorLeft (ModuleCat.of R A)).map u) at hn
  rw [hu]
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))
      (boundedAboveDerivedSingleFunctor.map u))).hom ≫
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (ModuleCat.ofHom (LinearMap.mul' R A))) =
    (boundedAboveDerivedTensorRightUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).hom.hom
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hr : (tensorLeft (ModuleCat.of R A)).map u ≫
      ModuleCat.ofHom (LinearMap.mul' R A) = (ρ_ (ModuleCat.of R A)).hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro r
    change a * algebraMap R A r = r • a
    rw [Algebra.smul_def, mul_comm]
  rw [hr]
  exact boundedAboveDerivedTensorModuleAugmentation_rightUnitor (ModuleCat.of R A)

end SerrePositivity
