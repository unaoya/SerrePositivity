module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction

/-!
分割で生成：docstring を書き直すこと
 # Reedy cofibrancy of standard simplices under a left Quillen functor

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

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (F : SSet.{v} ⥤ C) [F.IsLeftAdjoint]

variable (K : SSet.{v}) [K.Nonsingular] [K.Finite]

variable [ModelCategory C] [ModelCategory SSet.{v}] [IsLeftQuillen F]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma boundary_cofibration (n : ℕ) :
    cofibrations C (_root_.SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor.inclusion (SSet.boundary.{v} n) (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F)) := by
  have : Cofibration (SSet.boundary.{v} n).ι := by
    rw [cofibration_iff, hcof]
    infer_instance
  have := map_cofibration F (SSet.boundary.{v} n).ι
  have h := (cofibrations C).comp_mem _ _
    ((cofibrations C).of_isIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso F (SSet.boundary.{v} n).toSSet).hom)
    (mem_cofibrations (F.map (SSet.boundary.{v} n).ι))
  exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion F (SSet.boundary.{v} n)) ▸ h

include hcof in
lemma reedy_cofibrant : reedyLeft simplex (cofibrations C) (initial.to (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F)) := by
  intro j
  induction j using SimplexCategory.rec with | _ n =>
  exact ((cofibrations C).arrow_iso_iff
    (latchingInitialArrowIso simplex (SimplexCategory.mk n) (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F))).mp
      (((cofibrations C).arrow_iso_iff (_root_.SerrePositivity.HomotopyFunctionComplex.boundaryTensorArrowIso (_root_.SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial.diagram F) n)).mp
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.boundary_cofibration F hcof n))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
