module
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Exact pointwise colimits of coefficient functors -/
@[expose] public noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂} [Category.{v₂} B]
variable {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasColimitsOfShape J D]

/-- Exact diagram colimits preserve finite-limit preservation of coefficient functors. -/
instance functorColimit_preservesFiniteLimits (F : J ⥤ B ⥤ D)
    [HasExactColimitsOfShape J D] [∀ j, PreservesFiniteLimits (F.obj j)] :
    PreservesFiniteLimits (colimit F) := by
  have : PreservesFiniteLimits F.flip :=
    preservesFiniteLimits_of_evaluation _ (fun j => by
      change PreservesFiniteLimits (F.obj j)
      infer_instance)
  exact preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim F).symm

/-- Pointwise colimits preserve finite-colimit preservation of coefficient functors. -/
instance functorColimit_preservesFiniteColimits (F : J ⥤ B ⥤ D)
    [∀ j, PreservesFiniteColimits (F.obj j)] : PreservesFiniteColimits (colimit F) := by
  have : PreservesFiniteColimits F.flip :=
    preservesFiniteColimits_of_evaluation _ (fun j => by
      change PreservesFiniteColimits (F.obj j)
      infer_instance)
  exact preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim F).symm

end SerrePositivity
