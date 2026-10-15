module
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Additivity and linearity of the categorical colimit functor -/
@[expose] public section
noncomputable section
universe v w u t
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {J : Type t} [Category.{w} J]
variable {B : Type u} [Category.{v} B] [Preadditive B] [HasColimitsOfShape J B]

/-- Taking colimits is additive in natural transformations of arbitrary diagrams. -/
instance colimitFunctor_additive : (colim : (J ⥤ B) ⥤ B).Additive where
  map_add {F G f g} := by
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_map, Preadditive.comp_add, colimit.ι_map, colimit.ι_map]
    simp only [NatTrans.app_add, Preadditive.add_comp]

/-- Taking colimits is linear in natural transformations. -/
instance colimitFunctor_linear {A : Type*} [Semiring A] [Linear A B] :
    Functor.Linear A (colim : (J ⥤ B) ⥤ B) where
  map_smul f a := by
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_map, Linear.comp_smul, colimit.ι_map]
    simp only [NatTrans.app_smul, Linear.smul_comp]

end SerrePositivity
