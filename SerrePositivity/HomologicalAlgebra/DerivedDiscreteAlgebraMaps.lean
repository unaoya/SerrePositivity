module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBraided
public import Mathlib.Algebra.Algebra.Bilinear

/-! # Canonical multiplication and unit maps on actual discrete derived algebras

The maps use the established tensor augmentation. Their monoid laws are separate proof obligations.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The canonical derived multiplication induced by ordinary algebra multiplication. -/
def boundedAboveDerivedAlgebraMul (A : Type u) [CommRing A] [Algebra R A] :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)) ⟶
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A) :=
  ObjectProperty.homMk
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A)))

/-- The unit uses the existing tensor unit and its standard degree-zero comparison. -/
def boundedAboveDerivedAlgebraUnit (A : Type u) [CommRing A] [Algebra R A] :
    boundedAboveDerivedTensorUnit (R := R) ⟶
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A) :=
  ObjectProperty.homMk
    (boundedAboveDerivedTensorUnitSingleIso.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (Algebra.linearMap R A)))

/-- Under the standard tensor universal property the derived product is ordinary multiplication. -/
@[simp] lemma boundedAboveDerivedAlgebraMul_comparison
    (A : Type u) [CommRing A] [Algebra R A] :
    boundedAboveDerivedTensorModuleHomEquiv (ModuleCat.of R A) (ModuleCat.of R A)
      (ModuleCat.of R A) (boundedAboveDerivedAlgebraMul A).hom =
        ModuleCat.ofHom (LinearMap.mul' R A) := by
  change boundedAboveDerivedTensorModuleHomEquiv _ _ _ (_ ≫ _) = _
  rw [boundedAboveDerivedTensorModuleHomEquiv_postcomp,
    boundedAboveDerivedTensorModuleHomEquiv_augmentation, Category.id_comp]

/-- Algebra morphisms preserve the actual derived product map. -/
lemma boundedAboveDerivedAlgebraMul_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))) ≫
      boundedAboveDerivedAlgebraMul B =
    boundedAboveDerivedAlgebraMul A ≫
      boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap) := by
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
      (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap)))).hom ≫
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R B)).app _ ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (ModuleCat.ofHom (LinearMap.mul' R B))) =
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app _ ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom f.toLinearMap)
  rw [← Category.assoc, boundedAboveDerivedTensorModuleAugmentation_naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  have hm : (ModuleCat.ofHom f.toLinearMap ⊗ₘ ModuleCat.ofHom f.toLinearMap) ≫
      ModuleCat.ofHom (LinearMap.mul' R B) =
    ModuleCat.ofHom (LinearMap.mul' R A) ≫ ModuleCat.ofHom f.toLinearMap := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact (f.map_mul a b).symm
  exact congrArg (fun h =>
    (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app _ ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map h) hm

/-- Algebra morphisms preserve the actual derived unit map. -/
lemma boundedAboveDerivedAlgebraUnit_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    boundedAboveDerivedAlgebraUnit A ≫
        boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap) =
      boundedAboveDerivedAlgebraUnit B := by
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensorUnitSingleIso.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (Algebra.linearMap R A))) ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom f.toLinearMap) =
    boundedAboveDerivedTensorUnitSingleIso.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (Algebra.linearMap R B))
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hu : ModuleCat.ofHom (Algebra.linearMap R A) ≫ ModuleCat.ofHom f.toLinearMap =
      ModuleCat.ofHom (Algebra.linearMap R B) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact f.commutes r
  exact congrArg (fun h => boundedAboveDerivedTensorUnitSingleIso.hom ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map h) hu

/-- The standard single-object H0 comparisons identify the derived unit with algebraMap. -/
lemma boundedAboveDerivedAlgebraUnit_homology
    (A : Type u) [CommRing A] [Algebra R A] :
    (realizedSingleH0Iso R).inv.app (ModuleCat.of R R) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
          (boundedAboveDerivedAlgebraUnit A).hom ≫
        (realizedSingleH0Iso R).hom.app (ModuleCat.of R A) =
      ModuleCat.ofHom (Algebra.linearMap R A) := by
  let f := ModuleCat.ofHom (Algebra.linearMap R A)
  have hu : (boundedAboveDerivedAlgebraUnit A).hom =
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map f := by
    change (𝟙 _) ≫ _ = _
    exact Category.id_comp _
  rw [hu]
  have hn := (realizedSingleH0Iso R).hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

end SerrePositivity
