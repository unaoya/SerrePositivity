module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
public import Mathlib.CategoryTheory.Category.Cat

/-! # A strict simplicial diagram of categories of relative bar-action lifts

Objects retain the original base objects. Every simplex of morphisms retains
its base arrow and the entire extension family. The diagram is auxiliary
and is not a small SSet-valued strictification on the original base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def functor : SimplexCategoryᵒᵖ ⥤ Cat.{max u v, u} where
  obj n := Cat.of (OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
    (SSet.stdSimplex.{max u v}.obj n.unop))
  map θ := (OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map θ.unop)).toCatHom
  map_id n := by
    apply Cat.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map (𝟙 n.unop)) = _
    rw [CategoryTheory.Functor.map_id SSet.stdSimplex, OrdinaryBarChoiceCategory.reindex_id]
    rfl
  map_comp f g := by
    apply Cat.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib
      (SSet.stdSimplex.map (g.unop ≫ f.unop)) = _
    rw [SSet.stdSimplex.map_comp, OrdinaryBarChoiceCategory.reindex_comp]
    rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
