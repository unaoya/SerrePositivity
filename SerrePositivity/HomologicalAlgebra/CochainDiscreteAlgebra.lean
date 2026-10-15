module
public import SerrePositivity.HomologicalAlgebra.CochainSingleMonoidal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Algebra.Bilinear

/-! # Canonical algebra structures on ordinary modules and their actual degree-zero cochains -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R]

/-- The ordinary algebra multiplication and algebra map form a monoid object in modules. -/
@[instance_reducible] def moduleAlgebraMonObj (A : Type u) [CommRing A] [Algebra R A] :
    MonObj (ModuleCat.of R A) where
  one := ModuleCat.ofHom (Algebra.linearMap R A)
  mul := ModuleCat.ofHom (LinearMap.mul' R A)
  one_mul := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro r
    apply LinearMap.ext
    intro a
    exact (Algebra.smul_def r a).symm
  mul_one := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro r
    change a * algebraMap R A r = r • a
    exact (mul_comm a (algebraMap R A r)).trans (Algebra.smul_def (R := R) r a).symm
  mul_assoc := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro a b c
    exact mul_assoc a b c

/-- The proved strong monoidal degree-zero embedding supplies the actual cochain algebra. -/
@[instance_reducible] def cochainAlgebraMonObj (A : Type u) [CommRing A] [Algebra R A] :
    MonObj (cochainSingleZero (ModuleCat.of R A)) := by
  letI := moduleAlgebraMonObj (R := R) A
  exact (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).monObjObj (ModuleCat.of R A)

/-- The canonical cochain product obeys associativity for the actual total tensor associator. -/
lemma cochainAlgebraMul_assoc (A : Type u) [CommRing A] [Algebra R A] :
    let K := cochainSingleZero (ModuleCat.of R A)
    let μ := (cochainSingleTensorIso (ModuleCat.of R A) (ModuleCat.of R A)).hom ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))
    cochainTensorMap μ (𝟙 K) ≫ μ =
      (cochainTensorAssociator K K K).hom ≫ cochainTensorMap (𝟙 K) μ ≫ μ := by
  let := cochainAlgebraMonObj (R := R) A
  exact MonObj.mul_assoc (cochainSingleZero (ModuleCat.of R A))

/-- The standard algebra product is associative after arbitrary chain augmentations. -/
lemma cochainAlgebraMul_augmented_assoc (A : Type u) [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ε : P ⟶ cochainSingleZero (ModuleCat.of R A)) :
    let μ := (cochainSingleTensorIso (ModuleCat.of R A) (ModuleCat.of R A)).hom ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))
    cochainTensorMap (cochainTensorMap ε ε ≫ μ) ε ≫ μ =
      (cochainTensorAssociator P P P).hom ≫
        cochainTensorMap ε (cochainTensorMap ε ε ≫ μ) ≫ μ := by
  let K := cochainSingleZero (ModuleCat.of R A)
  let μ := (cochainSingleTensorIso (ModuleCat.of R A) (ModuleCat.of R A)).hom ≫
    (CochainComplex.singleFunctor (ModuleCat R) 0).map
      (ModuleCat.ofHom (LinearMap.mul' R A))
  have hL : cochainTensorMap (cochainTensorMap ε ε ≫ μ) ε =
      cochainTensorMap (cochainTensorMap ε ε) ε ≫ cochainTensorMap μ (𝟙 K) := by
    rw [cochainTensorMap_comp]
    erw [Category.comp_id]
  have hR : cochainTensorMap ε (cochainTensorMap ε ε ≫ μ) =
      cochainTensorMap ε (cochainTensorMap ε ε) ≫ cochainTensorMap (𝟙 K) μ := by
    rw [cochainTensorMap_comp]
    erw [Category.comp_id]
  change cochainTensorMap (cochainTensorMap ε ε ≫ μ) ε ≫ μ =
    (cochainTensorAssociator P P P).hom ≫
      cochainTensorMap ε (cochainTensorMap ε ε ≫ μ) ≫ μ
  rw [hL, hR, Category.assoc, cochainAlgebraMul_assoc]
  have hn : cochainTensorMap (cochainTensorMap ε ε) ε ≫
      (cochainTensorAssociator K K K).hom =
    (cochainTensorAssociator P P P).hom ≫ cochainTensorMap ε (cochainTensorMap ε ε) :=
      MonoidalCategory.associator_naturality ε ε ε
  rw [← Category.assoc (cochainTensorMap (cochainTensorMap ε ε) ε), hn]
  simp only [Category.assoc]
  rfl

end SerrePositivity
