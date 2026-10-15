module
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Pointwise colimits of additive and linear coefficient functors -/
@[expose] public section
noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasColimitsOfShape J D]

/-- Actual pointwise colimits preserve additivity of the coefficient functors. -/
instance functorColimit_additive (F : J ⥤ B ⥤ D) [∀ j, (F.obj j).Additive] :
    (colimit F).Additive where
  map_add {X Y f g} := by
    apply colimit_obj_ext
    intro j
    rw [← (colimit.ι F j).naturality (f + g), (F.obj j).map_add,
      Preadditive.add_comp, Preadditive.comp_add,
      (colimit.ι F j).naturality f, (colimit.ι F j).naturality g]

variable {A : Type*} [Semiring A] [Linear A B] [Linear A D]

/-- Actual pointwise colimits preserve linearity over the coefficient algebra. -/
instance functorColimit_linear (F : J ⥤ B ⥤ D) [∀ j, Functor.Linear A (F.obj j)] :
    Functor.Linear A (colimit F) where
  map_smul f r := by
    apply colimit_obj_ext
    intro j
    rw [← (colimit.ι F j).naturality (r • f), (F.obj j).map_smul,
      Linear.smul_comp, Linear.comp_smul, (colimit.ι F j).naturality f]

end SerrePositivity
