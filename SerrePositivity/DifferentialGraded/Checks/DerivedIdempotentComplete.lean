module
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 非有界導来圏の可算telescopeと冪等分裂の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : IsIdempotentComplete (DerivedModuleCategory A D) := inferInstance

example (X : DerivedModuleCategory A D) (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : DerivedModuleCategory A D) (i : Y ⟶ X) (e : X ⟶ Y),
      i ≫ e = 𝟙 Y ∧ e ≫ i = p :=
  idempotent_split_of_countable_coproduct X p hp

example : IsIdempotentComplete (DerivedModuleCategory (ZMod 2) PUnit.{1}) := inferInstance

#print axioms idempotentTelescopeShift
#print axioms idempotentTelescopeMap
#print axioms idempotentTelescopeRetraction
#print axioms idempotentTelescopeMap_retraction
#print axioms idempotentTelescopeMap_mono
#print axioms idempotent_split_of_countable_coproduct
#print axioms moduleDerivedIsIdempotentComplete
