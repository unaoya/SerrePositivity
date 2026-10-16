module
public import SerrePositivity.DifferentialGraded.Category.IdempotentTelescope
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Derived.Triangulated

/-! # 指定された非有界dg加群導来圏の冪等完備性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleDerivedIsIdempotentComplete : IsIdempotentComplete (DerivedModuleCategory A D) where
  idempotents_split X p hp := idempotent_split_of_countable_coproduct X p hp

end SerrePositivity.DifferentialGraded
