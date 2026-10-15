module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Diagonals of double cosimplicial objects

The construction and augmentation maps are ordinary category theory. Weak
augmentation statements use only the actual iterated Reedy resolution;
no diagonal cofibrancy or invariance theorem is assumed here.
-/

@[expose] public section
universe v u vI uI
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalFrame
variable {C : Type u} [Category.{v} C] {I : Type uI} [Category.{vI} I]

abbrev obj (A : I ⥤ I ⥤ C) : I ⥤ C := Functor.diag I ⋙ Functor.uncurry.obj A

@[simp]
lemma obj_obj (A : I ⥤ I ⥤ C) (i : I) : (obj A).obj i = (A.obj i).obj i := rfl

@[simp]
lemma obj_map (A : I ⥤ I ⥤ C) {i j : I} (f : i ⟶ j) :
    (obj A).map f = (A.map f).app i ≫ (A.obj j).map f := rfl

/-- Restrict a natural transformation of double diagrams to the diagonal. -/
def map {A A' : I ⥤ I ⥤ C} (a : A ⟶ A') : obj A ⟶ obj A' :=
  Functor.whiskerLeft (Functor.diag I) (Functor.uncurry.map a)

/-- The diagonal of an outer constant diagram is naturally its value. -/
def constantIso (B : I ⥤ C) : obj ((Functor.const I).obj B) ≅ B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    change (𝟙 _ ≫ B.map f) ≫ 𝟙 _ = 𝟙 _ ≫ B.map f
    simp only [Category.id_comp, Category.comp_id])

/-- An outer augmentation induces an actual augmentation of the diagonal. -/
def augmentation {A : I ⥤ I ⥤ C} {B : I ⥤ C}
    (a : A ⟶ (Functor.const I).obj B) : obj A ⟶ B where
  app i := (a.app i).app i
  naturality {i j} f := by
    change ((A.map f).app i ≫ (A.obj j).map f) ≫ (a.app j).app j =
      (a.app i).app i ≫ B.map f
    have ho := congr_app (a.naturality f) i
    change (A.map f).app i ≫ (a.app j).app i = (a.app i).app i ≫ 𝟙 _ at ho
    calc
      _ = (A.map f).app i ≫ ((a.app j).app i ≫ B.map f) := by
        rw [Category.assoc, (a.app j).naturality]
        rfl
      _ = _ := by rw [← Category.assoc, ho, Category.comp_id]

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev resolution (B : SimplexCategory ⥤ C) := Reedy.cosimplicialResolution B

abbrev resolutionObj (B : SimplexCategory ⥤ C) : SimplexCategory ⥤ C :=
  obj (resolution B).obj

abbrev resolutionAugmentation (B : SimplexCategory ⥤ C) : resolutionObj B ⟶ B :=
  augmentation (resolution B).augmentation

lemma resolutionAugmentation_weakEquivalence (B : SimplexCategory ⥤ C)
    (n : SimplexCategory) : weakEquivalences C ((resolutionAugmentation B).app n) :=
  (resolution B).augmentation_weakEquivalence n n

lemma resolutionObj_homotopicallyConstant (B : SimplexCategory ⥤ C)
    (hB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((resolutionObj B).map f) := by
  have h := (resolutionAugmentation B).naturality f
  exact (weakEquivalences C).of_postcomp _ _
    (resolutionAugmentation_weakEquivalence B m)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _
      (resolutionAugmentation_weakEquivalence B n) (hB f))

end SerrePositivity.HomotopyFunctionComplex.DiagonalFrame
