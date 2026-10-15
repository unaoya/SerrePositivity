module
public import SerrePositivity.HomologicalAlgebra.DerivedAlgebraMorphisms
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The actual standard derived tensor augmentation is an algebra morphism -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The canonical algebra morphism from the actual derived tensor to the ordinary tensor. -/
def boundedAboveDerivedTensorAlgebraAugmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedTensorAlgebra (R := R) S T ⟶
      boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T) := by
  let B := boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)
  let f := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
  let g := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
  letI := B.mon
  letI := B.comm
  letI : IsMonHom B.mon.mul :=
    { one_hom := by
        dsimp only [MonObj.tensorObj.one_def]
        rw [Category.assoc, MonObj.one_mul_hom, Iso.inv_hom_id_assoc]
      mul_hom := by
        dsimp only [MonObj.tensorObj.mul_def]
        simpa only [Category.assoc] using MonObj.mul_mul_mul_comm B.X }
  let μ : B.toMon ⊗ B.toMon ⟶ B.toMon := Mon.Hom.mk B.mon.mul
  let h : (boundedAboveDerivedAlgebra (R := R) S).toMon ⊗
      (boundedAboveDerivedAlgebra (R := R) T).toMon ⟶ B.toMon := (f.hom ⊗ₘ g.hom) ≫ μ
  exact CommMon.homMk h

/-- Its underlying map is precisely the existing standard tensor augmentation. -/
lemma boundedAboveDerivedTensorAlgebraAugmentation_hom
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom =
      (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app (ModuleCat.of R T) := by
  let i := ModuleCat.ofHom
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toLinearMap
  let j := ModuleCat.ofHom
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toLinearMap
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map i) (boundedAboveDerivedSingleFunctor.map j))).hom ≫
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R (S ⊗[R] T))).app _ ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
          (ModuleCat.ofHom (LinearMap.mul' R (S ⊗[R] T)))) = _
  rw [← Category.assoc, boundedAboveDerivedTensorModuleAugmentation_naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hij : (i ⊗ₘ j) ≫ ModuleCat.ofHom (LinearMap.mul' R (S ⊗[R] T)) =
      𝟙 ((ModuleCat.of R S) ⊗ (ModuleCat.of R T)) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro t
    change (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = s ⊗ₜ[R] t
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hij]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The algebra augmentation is the product of the two ordinary tensor inclusion maps. -/
lemma boundedAboveDerivedTensorAlgebraAugmentation_map
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom =
      boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)).hom.hom
        (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)).hom.hom) ≫
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)).mon.mul := rfl

/-- The left factor and augmentation give the usual tensor inclusion as algebra maps. -/
lemma boundedAboveDerivedTensorAlgebraLeft_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫
        boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T =
      boundedAboveDerivedAlgebraMap
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) := by
  let C := boundedAboveDerivedAlgebra (R := R) S
  let D := boundedAboveDerivedAlgebra (R := R) T
  let B := boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)
  let f := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
  let g := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
  let := C.mon
  let := D.mon
  let := B.mon
  let : IsMonHom g.hom.hom := g.hom.isMonHom_hom
  apply CommMon.hom_ext
  simp only [CommMon.comp_hom]
  rw [boundedAboveDerivedTensorAlgebraLeft_hom, boundedAboveDerivedTensorAlgebraAugmentation_map]
  change ((ρ_ C.X).inv ≫ (C.X ◁ D.mon.one)) ≫
    (f.hom.hom ⊗ₘ g.hom.hom) ≫ B.mon.mul = f.hom.hom
  rw [← id_tensorHom]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙 C.X ⊗ₘ D.mon.one), tensorHom_comp_tensorHom,
    Category.id_comp, IsMonHom.one_hom, MonObj.mul_one_hom, Iso.inv_hom_id_assoc]

/-- The right factor and augmentation give the usual tensor inclusion as algebra maps. -/
lemma boundedAboveDerivedTensorAlgebraRight_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫
        boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T =
      boundedAboveDerivedAlgebraMap
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) := by
  let C := boundedAboveDerivedAlgebra (R := R) S
  let D := boundedAboveDerivedAlgebra (R := R) T
  let B := boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)
  let f := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
  let g := boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
  let := C.mon
  let := D.mon
  let := B.mon
  let : IsMonHom f.hom.hom := f.hom.isMonHom_hom
  apply CommMon.hom_ext
  simp only [CommMon.comp_hom]
  rw [boundedAboveDerivedTensorAlgebraRight_hom, boundedAboveDerivedTensorAlgebraAugmentation_map]
  change ((λ_ D.X).inv ≫ (C.mon.one ▷ D.X)) ≫
    (f.hom.hom ⊗ₘ g.hom.hom) ≫ B.mon.mul = g.hom.hom
  rw [← tensorHom_id]
  simp only [Category.assoc]
  rw [← Category.assoc (C.mon.one ⊗ₘ 𝟙 D.X), tensorHom_comp_tensorHom,
    Category.id_comp, IsMonHom.one_hom, MonObj.one_mul_hom, Iso.inv_hom_id_assoc]

end SerrePositivity
