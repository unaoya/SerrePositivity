module
public import SerrePositivity.HomologicalAlgebra.MonoidalPointAction
public import SerrePositivity.HomologicalAlgebra.DerivedSingleH0Algebra

/-! # Ordinary coefficient multiplication is the actual derived algebra point action -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The standard augmentation preserves the inverse left unitor at every discrete module. -/
lemma derivedTensorAugmentation_inv_leftUnitor (M : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedSingleFunctor.obj M)).inv.hom ≫
        (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R R)).app M =
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map (λ_ M).inv := by
  apply (cancel_mono ((DerivedCategory.singleFunctor (ModuleCat R) 0).map (λ_ M).hom)).mp
  rw [Category.assoc, boundedAboveDerivedTensorModuleAugmentation_leftUnitor,
    ← CategoryTheory.Functor.map_comp]
  change (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedSingleFunctor.obj M)).inv.hom ≫
    (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedSingleFunctor.obj M)).hom.hom = _
  rw [← InducedCategory.comp_hom]
  simp
  rfl

/-- An ordinary R-linear point acts by the original single map of multiplication. -/
lemma boundedAboveDerivedAlgebra_pointAction
    (A : Type u) [CommRing A] [Algebra R A]
    (f : ModuleCat.of R R ⟶ ModuleCat.of R A) :
    commMonPointAction (boundedAboveDerivedAlgebra (R := R) A)
        (boundedAboveDerivedSingleFunctor.map f) =
      boundedAboveDerivedSingleFunctor.map
        (ModuleCat.ofHom (LinearMap.mulLeft R (f.hom 1))) := by
  apply InducedCategory.hom_ext
  change (boundedAboveDerivedTensorLeftUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))).inv.hom ≫
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))))).hom ≫
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))) = _
  rw [← Category.assoc _ _ ((DerivedCategory.singleFunctor (ModuleCat R) 0).map _),
    boundedAboveDerivedTensorModuleAugmentation_naturality_left]
  simp only [← Category.assoc]
  erw [derivedTensorAugmentation_inv_leftUnitor]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg (DerivedCategory.singleFunctor (ModuleCat R) 0).map
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change LinearMap.mul' R A
    ((TensorProduct.map f.hom LinearMap.id) ((TensorProduct.lid R A).symm x)) = f.hom 1 * x
  simp

/-- Standard single H⁰ normalization gives the usual coefficient multiplication. -/
lemma boundedAboveDerivedAlgebra_pointAction_singleH0
    (A : Type u) [CommRing A] [Algebra R A] (b : A) :
    commMonPointAction (boundedAboveDerivedAlgebra (R := R) A)
      (boundedAboveUnitH0LinearEquiv (boundedAboveDerivedAlgebra (R := R) A).X
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R A) b)) =
      boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R b)) := by
  let f : ModuleCat.of R R ⟶ ModuleCat.of R A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R A b)
  have h := boundedAboveUnitH0LinearEquiv_single (ModuleCat.of R A) f
  have hf : f.hom 1 = b := by simp [f]
  rw [hf] at h
  erw [h]
  have hm := boundedAboveDerivedAlgebra_pointAction A f
  rw [hf] at hm
  exact hm

end SerrePositivity
