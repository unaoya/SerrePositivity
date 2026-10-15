module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ComponentClasses
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown

/-! # Cofibrations under the actual bisimplicial diagonal

The diagonal preserves monomorphisms and Reedy cofibrations. Reedy
cofibrancy of all bisimplicial sets reduces weak-equivalence preservation
to proving the remaining Quillen condition. That condition is not assumed
as a completed diagonal theorem in this module.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel

lemma diagonal_map_mono {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B') [Mono f] :
    Mono (diagonal.map f) := by
  have : ∀ n, Mono ((diagonal.map f).app n) := by
    intro n
    exact inferInstanceAs (Mono ((f.app n).app n))
  exact NatTrans.mono_of_mono_app _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma diagonal_map_reedyCofibration {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (f : B ⟶ B') (hf : reedyLeft simplexOp (cofibrations SSet.{v}) f) :
    cofibrations SSet.{v} (diagonal.map f) := by
  have : ∀ n, Mono (f.app n) := by
    intro n
    change MorphismProperty.monomorphisms SSet.{v} (f.app n)
    rw [← hcof]
    exact cofibration_app simplexOp f hf n
  have : Mono f := NatTrans.mono_of_mono_app _
  rw [hcof]
  exact diagonal_map_mono f

include hcof in
/-- The formal reduction using actual Reedy cofibrancy. The missing Quillen
proof must be supplied before this becomes an unconditional diagonal theorem. -/
lemma diagonal_map_weakEquivalence_of_isLeftQuillen
    (hQ : let := simplexOpModelCategory SSet.{v}; Quillen.IsLeftQuillen diagonal.{v})
    {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (diagonal.map f) := by
  have hB := isCofibrant hcof B
  have hB' := isCofibrant hcof B'
  let := simplexOpModelCategory SSet.{v}
  have : Quillen.IsLeftQuillen diagonal.{v} := hQ
  have : IsCofibrant B := hB
  have : IsCofibrant B' := hB'
  have : WeakEquivalence f := ⟨hf⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant diagonal f)

end SerrePositivity.BisimplicialModel
