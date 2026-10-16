module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension

/-! # The first two free-resolution faces of the actual choice-cover functor

Both faces have the same entire base projection. The degeneracy splits
both of them as strict functor equalities. Their lifted values are not
asserted equal before supplying a relative comparison.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def faceZero (P : SSet.{max u v}) : Paths (Paths (Cᵒᵖ × C)) ⥤
    OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib P :=
  FreePathResolution.counit (Paths (Cᵒᵖ × C)) ⋙
    OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P

def faceOne (P : SSet.{max u v}) : Paths (Paths (Cᵒᵖ × C)) ⥤
    OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib P :=
  FreePathResolution.map (FreePathResolution.counit (Cᵒᵖ × C)) ⋙
    OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P

lemma projection_equal (P : SSet.{max u v}) :
    faceZero (C := C) hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P =
      faceOne hcof hfib P ⋙ OrdinaryBarChoiceCategory.projection hcof hfib P := by
  simp only [faceZero, faceOne, CategoryTheory.Functor.assoc,
    OrdinaryBarFreeDiagramExtension.freeCover_projection, FreePathResolution.lift_identity]
  exact (FreePathResolution.counit_naturality (FreePathResolution.counit (Cᵒᵖ × C))).symm

lemma degeneracy_faceZero (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ faceZero hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P := by
  change (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolution.counit (Paths (Cᵒᵖ × C))) ⋙
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P = _
  rw [FreePathResolution.left_counit, CategoryTheory.Functor.id_comp]

lemma degeneracy_faceOne (P : SSet.{max u v}) :
    FreePathResolution.duplicate (Cᵒᵖ × C) ⋙ faceOne hcof hfib P =
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P := by
  change (FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    FreePathResolution.map (FreePathResolution.counit (Cᵒᵖ × C))) ⋙
      OrdinaryBarFreeDiagramExtension.freeCover hcof hfib P = _
  rw [FreePathResolution.right_counit, CategoryTheory.Functor.id_comp]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces
