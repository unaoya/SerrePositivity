module
public import SerrePositivity.DifferentialGraded.Module.ColimitHom
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # U10b5b：主Hom endの余極限から極限への普遍性 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {J : Type w} [Category.{w'} J] [Small.{u} J]
    {F : J ⥤ ModuleCategory A D} {c : Cocone F} (hc : IsColimit c)
    (N : ModuleCategory A D) : IsLimit (moduleColimitHomCone A D c N) :=
  moduleColimitHomIsLimit A D hc N

example (M : ℕ → ModuleCategory A D) (f : ∀ n, M n ⟶ M (n + 1))
    {c : Cocone (Functor.ofSequence f)} (hc : IsColimit c) (N : ModuleCategory A D) :
    IsLimit (moduleColimitHomCone A D c N) := moduleColimitHomIsLimit A D hc N

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleHomSourceDiagram
#print axioms moduleColimitHomCone
#print axioms moduleColimitHomUncurryCocone
#print axioms moduleColimitHomLift
#print axioms moduleColimitHomLift_π
#print axioms moduleColimitHomIsLimit
