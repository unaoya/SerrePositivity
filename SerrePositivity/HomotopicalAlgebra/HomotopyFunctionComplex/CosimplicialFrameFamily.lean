module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-! # Cosimplicial frame families with objectwise weak augmentations

The augmentation is not required to be a Reedy trivial fibration. This
includes the actual standard tensor frame while retaining that distinction
from the stronger chosen resolution families.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

structure CosimplicialFrameFamily where
  obj : C ⥤ (SimplexCategory ⥤ C)
  augmentation : obj ⟶ Functor.const SimplexCategory
  cofibrant : ∀ X, reedyLeft simplex (cofibrations C) (initial.to (obj.obj X))
  weak : ∀ X n, weakEquivalences C ((augmentation.app X).app n)

namespace CosimplicialFrameFamily

def ofResolution (q : CofibrantResolutionFamily (C := C) simplex) :
    CosimplicialFrameFamily (C := C) where
  obj := q.obj
  augmentation := q.augmentation
  cofibrant := q.cofibrant
  weak X n := (q.atObject X).augmentation_weakEquivalence n

lemma homotopicallyConstant (q : CosimplicialFrameFamily (C := C)) (X : C)
    {n m : SimplexCategory} (f : n ⟶ m) : weakEquivalences C ((q.obj.obj X).map f) := by
  have h := (q.augmentation.app X).naturality f
  change (q.obj.obj X).map f ≫ (q.augmentation.app X).app m =
    (q.augmentation.app X).app n ≫ 𝟙 X at h
  have he : (q.obj.obj X).map f ≫ (q.augmentation.app X).app m =
      (q.augmentation.app X).app n := h.trans (Category.comp_id _)
  have hw : weakEquivalences C ((q.obj.obj X).map f ≫ (q.augmentation.app X).app m) :=
    he.symm ▸ q.weak X n
  exact (weakEquivalences C).of_postcomp _ _ (q.weak X m) hw

end CosimplicialFrameFamily
end SerrePositivity.HomotopyFunctionComplex
