module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport

/-! # The strict mixed Hom functor on actual pairs of cosimplicial diagrams -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
variable {C : Type u} [Category.{v} C]

def functor : (SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ ⥤ SSet.{v} where
  obj X := obj X.1.unop X.2.unop
  map f := map f.1.unop f.2.unop
  map_id X := map_id X.1.unop X.2.unop
  map_comp f g := map_comp f.1.unop g.1.unop f.2.unop g.2.unop

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
