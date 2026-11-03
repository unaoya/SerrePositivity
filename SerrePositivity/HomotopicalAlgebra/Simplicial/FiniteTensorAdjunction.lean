module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic

/-! # Reedy cofibrancy of standard simplices under a left Quillen functor

Finite nonsingular presentations are actual colimits of standard simplices.
A left adjoint preserves these presentations, identifying their constructed
finite tensor with its own value. Boundary inclusions then prove Reedy
cofibrancy, without a separate assumed latching condition.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (F : SSet.{v} ⥤ C) [F.IsLeftAdjoint]

abbrev diagram : SimplexCategory ⥤ C := SSet.stdSimplex ⋙ F

end SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial
