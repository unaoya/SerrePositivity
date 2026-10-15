module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryHom

/-! # bimoduleのuncurrying Hom射・単位保存の受入 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (M : Bimodule A B C) (x : DGTensorCategory A Bᵒᵖ C) :
    eId (Complex A) x ≫ M.uncurryHom x x =
      identity (M.value x.1.unop x.2) := M.uncurryHom_identity x
#print axioms Bimodule.uncurryHom
#print axioms Bimodule.uncurryHom_apply
#print axioms Bimodule.complex_unitElement
#print axioms Bimodule.leftCochain_unit
#print axioms Bimodule.uncurryHom_unit
#print axioms Bimodule.uncurryHom_identity
