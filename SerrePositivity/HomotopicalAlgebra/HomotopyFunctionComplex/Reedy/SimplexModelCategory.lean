module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite

/-! # The Reedy model categories of simplicial and cosimplicial objects

Both constructions work over every model category, without assuming
functorial source factorization or infinite limits or colimits.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable (C : Type u) [Category.{v} C] [ModelCategory C]

@[instance_reducible]
def simplexModelCategory : ModelCategory (SimplexCategory ⥤ C) :=
  modelCategory simplex (fun _ _ h ↦ SimplexCategory.ext h)
    (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)

@[instance_reducible]
def simplexOpModelCategory : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  modelCategory simplexOp (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

@[simp]
lemma simplexModelCategory_weakEquivalences :
    (simplexModelCategory C).categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences C).functorCategory SimplexCategory := rfl

@[simp]
lemma simplexOpModelCategory_weakEquivalences :
    (simplexOpModelCategory C).categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ := rfl

@[simp]
lemma simplexModelCategory_fibrations :
    (simplexModelCategory C).categoryWithFibrations.fibrations =
      reedyRight simplex (fibrations C) := rfl

@[simp]
lemma simplexOpModelCategory_fibrations :
    (simplexOpModelCategory C).categoryWithFibrations.fibrations =
      reedyRight simplexOp (fibrations C) := rfl

@[simp]
lemma simplexModelCategory_cofibrations :
    (simplexModelCategory C).categoryWithCofibrations.cofibrations =
      reedyLeft simplex (cofibrations C) := rfl

@[simp]
lemma simplexOpModelCategory_cofibrations :
    (simplexOpModelCategory C).categoryWithCofibrations.cofibrations =
      reedyLeft simplexOp (cofibrations C) := rfl

end SerrePositivity.Reedy
