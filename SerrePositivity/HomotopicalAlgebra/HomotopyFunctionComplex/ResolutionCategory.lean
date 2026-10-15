module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-! # All cosimplicial resolutions over an arbitrary model category

No functorial factorization is chosen. Morphisms record a base map and an
actual map of resolutions over it. Every base map lifts between every pair
of resolutions. The chosen lifts are not asserted to form a functor.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex

structure ResolutionObject (C : Type u) [Category.{v} C] [ModelCategory C] where
  base : C
  resolution : CofibrantResolution simplex base

namespace ResolutionObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]

@[ext]
structure Hom (X Y : ResolutionObject C) where
  base : X.base ⟶ Y.base
  diagram : X.resolution.obj ⟶ Y.resolution.obj
  over : diagram ≫ Y.resolution.augmentation =
    X.resolution.augmentation ≫ (Functor.const SimplexCategory).map base

instance : Category (ResolutionObject C) where
  Hom := Hom
  id X := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp f g := ⟨f.base ≫ g.base, f.diagram ≫ g.diagram, by
    rw [Category.assoc, g.over, ← Category.assoc, f.over]
    simp only [Category.assoc, Functor.map_comp]⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp only [Category.assoc]

/-- Forget the resolution, retaining its augmentation target. -/
def projection : ResolutionObject C ⥤ C where
  obj X := X.base
  map f := f.base

/-- The actual cosimplicial diagram, functorial in all resolution morphisms. -/
def diagrams : ResolutionObject C ⥤ SimplexCategory ⥤ C where
  obj X := X.resolution.obj
  map f := f.diagram

/-- Ordinary model factorization supplies objects, without a functorial choice. -/
abbrev ofObject (X : C) : ResolutionObject C := ⟨X, cosimplicialResolution X⟩

/-- A lift of a base map. No compatibility of independently chosen lifts is claimed. -/
def lift {X Y : ResolutionObject C} (f : X.base ⟶ Y.base) : X ⟶ Y := by
  let := simplexModelCategory C
  have : Cofibration (initial.to X.resolution.obj) := ⟨X.resolution.cofibrant⟩
  have : Fibration Y.resolution.augmentation :=
    ⟨fun j => (Y.resolution.trivial j).1⟩
  have : WeakEquivalence Y.resolution.augmentation :=
    ⟨Y.resolution.augmentation_weakEquivalence⟩
  let sq : CommSq (initial.to Y.resolution.obj) (initial.to X.resolution.obj)
      Y.resolution.augmentation
      (X.resolution.augmentation ≫ (Functor.const SimplexCategory).map f) :=
    ⟨by apply initial.hom_ext⟩
  exact ⟨f, sq.lift, sq.fac_right⟩

@[simp]
lemma lift_base {X Y : ResolutionObject C} (f : X.base ⟶ Y.base) :
    (lift f).base = f := rfl

/-- Fullness is an existence statement; it supplies no strict section. -/
instance : projection (C := C) |>.Full where
  map_surjective f := ⟨lift f, rfl⟩

lemma diagram_weakEquivalence {X Y : ResolutionObject C} (f : X ⟶ Y)
    (hf : weakEquivalences C f.base) (n : SimplexCategory) :
    weakEquivalences C (f.diagram.app n) := by
  have h := congr_app f.over n
  change f.diagram.app n ≫ Y.resolution.augmentation.app n =
    X.resolution.augmentation.app n ≫ f.base at h
  exact (weakEquivalences C).of_postcomp _ _
    (Y.resolution.augmentation_weakEquivalence n)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _
      (X.resolution.augmentation_weakEquivalence n) hf)

end ResolutionObject
end SerrePositivity.HomotopyFunctionComplex
