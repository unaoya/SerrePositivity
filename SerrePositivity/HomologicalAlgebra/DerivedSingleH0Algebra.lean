module
public import SerrePositivity.HomologicalAlgebra.UnitHomologyNormalization
public import SerrePositivity.HomologicalAlgebra.DerivedAlgebraObjects
public import Mathlib.Algebra.Algebra.Equiv

/-! # The actual H⁰ algebra of a discrete algebra has its ordinary multiplication -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The tensor augmentation at the unit preserves the canonical inverse unitor. -/
lemma derivedTensorUnit_augmentation_invUnitor :
    (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedTensorUnit (R := R))).inv.hom ≫
      (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R R)).app (ModuleCat.of R R) =
    (DerivedCategory.singleFunctor (ModuleCat R) 0).map (λ_ (ModuleCat.of R R)).inv := by
  apply (cancel_mono ((DerivedCategory.singleFunctor (ModuleCat R) 0).map
    (λ_ (ModuleCat.of R R)).hom)).mp
  rw [Category.assoc, boundedAboveDerivedTensorModuleAugmentation_leftUnitor,
    ← CategoryTheory.Functor.map_comp]
  change (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedTensorUnit (R := R))).inv.hom ≫
      (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedTensorUnit (R := R))).hom.hom = _
  rw [← InducedCategory.comp_hom]
  simp
  rfl

/-- Ordinary maps from R multiply by the original derived multiplication. -/
lemma derivedSingle_points_mul (A : Type u) [CommRing A] [Algebra R A]
    (f g : ModuleCat.of R R ⟶ ModuleCat.of R A) :
    ((λ_ (𝟙_ (DerivedCategory.Minus (ModuleCat R)))).inv ≫
      (boundedAboveDerivedSingleFunctor.map f ⊗ₘ boundedAboveDerivedSingleFunctor.map g) ≫
      boundedAboveDerivedAlgebraMul (R := R) A).hom =
    (DerivedCategory.singleFunctor (ModuleCat R) 0).map
      ((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫ ModuleCat.ofHom (LinearMap.mul' R A)) := by
  change (boundedAboveDerivedTensorLeftUnitor (boundedAboveDerivedTensorUnit (R := R))).inv.hom ≫
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g))).hom ≫
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))) = _
  rw [← Category.assoc _ _ ((DerivedCategory.singleFunctor (ModuleCat R) 0).map _),
    boundedAboveDerivedTensorModuleAugmentation_naturality]
  simp only [← Category.assoc]
  erw [derivedTensorUnit_augmentation_invUnitor]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- The bounded-above unit comparison sends a standard single class to its ordinary point map. -/
lemma boundedAboveUnitH0LinearEquiv_single (M : ModuleCat.{u} R)
    (f : ModuleCat.of R R ⟶ M) :
    boundedAboveUnitH0LinearEquiv (boundedAboveDerivedSingleFunctor.obj M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app M
          (f.hom 1)) = boundedAboveDerivedSingleFunctor.map f := by
  apply InducedCategory.hom_ext
  exact derivedUnitH0NaturalLinearEquiv_single M f

/-- The ordinary product map on point tensors evaluates to the product of their values on one. -/
lemma module_point_product_one (A : Type u) [CommRing A] [Algebra R A]
    (f g : ModuleCat.of R R ⟶ ModuleCat.of R A) :
    (((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫
      ModuleCat.ofHom (LinearMap.mul' R A)).hom (1 : R)) = f.hom 1 * g.hom 1 := by
  change LinearMap.mul' R A
    ((TensorProduct.map f.hom g.hom) ((TensorProduct.lid R R).symm 1)) = _
  simp

/-- The canonical single H⁰ inverse respects the actual derived H⁰ product. -/
lemma derivedSingleH0_inv_mul (A : Type u) [CommRing A] [Algebra R A] (x y : A) :
    let : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R A) (x * y) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R A) x *
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R A) y := by
  let : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
  let f : ModuleCat.of R R ⟶ ModuleCat.of R A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R A x)
  let g : ModuleCat.of R R ⟶ ModuleCat.of R A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R A y)
  have hx : f.hom 1 = x := by simp [f]
  have hy : g.hom 1 = y := by simp [g]
  let h := (λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫
    ModuleCat.ofHom (LinearMap.mul' R A)
  have hh : h.hom 1 = x * y := by rw [module_point_product_one, hx, hy]
  apply (boundedAboveUnitH0LinearEquiv
    (boundedAboveDerivedAlgebra (R := R) A).X).injective
  rw [derivedH0_mul_normalization]
  change boundedAboveUnitH0LinearEquiv (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R A) (x * y)) = _
  have hf := boundedAboveUnitH0LinearEquiv_single (ModuleCat.of R A) f
  have hg := boundedAboveUnitH0LinearEquiv_single (ModuleCat.of R A) g
  have hn := boundedAboveUnitH0LinearEquiv_single (ModuleCat.of R A) h
  rw [hx] at hf
  rw [hy] at hg
  rw [hh] at hn
  erw [hf, hg, hn]
  apply InducedCategory.hom_ext
  exact (derivedSingle_points_mul A f g).symm

/-- The standard single H⁰ comparison is a ring equivalence for the actual derived product. -/
def derivedSingleH0RingEquiv (A : Type u) [CommRing A] [Algebra R A] :
    letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
    ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) ≃+* A := by
  letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
  let e : A ≃+* ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
    { ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R A)).toLinearEquiv.symm.toAddEquiv with
      map_mul' := derivedSingleH0_inv_mul A }
  exact e.symm

/-- The same canonical comparison preserves the original R-algebra structure. -/
def derivedSingleH0AlgEquiv (A : Type u) [CommRing A] [Algebra R A] :
    letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
    letI : Algebra R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) A)
    ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) ≃ₐ[R] A := by
  letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
  letI : Algebra R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) A)
  exact AlgEquiv.ofLinearEquiv
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
      (ModuleCat.of R A)).toLinearEquiv
    (derivedSingleH0RingEquiv A).map_one (derivedSingleH0RingEquiv A).map_mul

/-- Its function is exactly the existing standard single H⁰ isomorphism. -/
theorem derivedSingleH0AlgEquiv_apply (A : Type u) [CommRing A] [Algebra R A]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A))) :
    letI : CommRing
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) A)
    letI : Algebra R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)) :=
      derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) A)
    derivedSingleH0AlgEquiv (R := R) A x =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R A) x := rfl

end SerrePositivity
