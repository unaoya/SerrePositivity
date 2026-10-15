module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingMonomorphisms
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.CofibrantBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexModelCategory
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Every bisimplicial set is Reedy cofibrant

Evaluation of the actual latching comparison agrees, through the colimit
preservation isomorphism, with a simplicial-set latching comparison in Type.
Eilenberg--Zilber gives its injectivity. No splitting in SSet is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel

abbrev column (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) (k : SimplexCategoryᵒᵖ) : SSet.{v} :=
  B ⋙ (evaluation SimplexCategoryᵒᵖ (Type v)).obj k

/-- The actual latching comparison commutes with evaluation via colimit preservation. -/
lemma evaluation_comparison (B : SimplexCategoryᵒᵖ ⥤ SSet.{v})
    (j k : SimplexCategoryᵒᵖ) :
    (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type v)).obj k)
      (latchingSource simplexOp j ⋙ B)).inv ≫
      ((latchingComparison simplexOp j).app B).app k =
        (latchingComparison simplexOp j).app (column B k) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type v)).obj k
  let D := latchingSource simplexOp j ⋙ B
  apply colimit.hom_ext
  intro a
  change colimit.ι (D ⋙ E) a ≫
      ((preservesColimitIso E D).inv ≫ E.map ((latchingComparison simplexOp j).app B)) = _
  rw [← Category.assoc, ι_preservesColimitIso_inv, ← E.map_comp]
  exact (congrArg E.map (colimit.ι_desc (latchingCocone simplexOp B j) a)).trans
    (colimit.ι_desc (latchingCocone simplexOp (column B k) j) a).symm

lemma latchingComparison_mono (B : SimplexCategoryᵒᵖ ⥤ SSet.{v})
    (j : SimplexCategoryᵒᵖ) : Mono ((latchingComparison simplexOp j).app B) := by
  have : ∀ k, Mono (((latchingComparison simplexOp j).app B).app k) := by
    intro k
    let e := preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type v)).obj k)
      (latchingSource simplexOp j ⋙ B)
    have : Mono ((latchingComparison simplexOp j).app (column B k)) :=
      SimplicialLatching.comparison_mono _ _
    have he : ((latchingComparison simplexOp j).app B).app k =
        e.hom ≫ (latchingComparison simplexOp j).app (column B k) := by
      rw [← evaluation_comparison B j k]
      exact (Iso.hom_inv_id_assoc e _).symm
    rw [he]
    infer_instance
  exact NatTrans.mono_of_mono_app _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma reedyCofibrant (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    reedyLeft simplexOp (cofibrations SSet.{v}) (initial.to B) := by
  intro j
  apply ((cofibrations SSet.{v}).arrow_iso_iff (latchingInitialArrowIso simplexOp j B)).mp
  rw [hcof]
  exact latchingComparison_mono B j

include hcof in
lemma isCofibrant (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    let := simplexOpModelCategory SSet.{v}
    IsCofibrant B := by
  let := simplexOpModelCategory SSet.{v}
  exact ⟨reedyCofibrant hcof B⟩

end SerrePositivity.BisimplicialModel
